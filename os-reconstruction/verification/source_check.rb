#!/usr/bin/env ruby
require 'set'
require 'json'

# Preserve token boundaries while masking strings and nested Lean comments.
def lean_code(path)
  source = File.binread(path)
  clean = +''.b
  depth = 0
  in_string = false
  index = 0
  while index < source.length
    pair = source[index, 2]
    char = source[index]
    if depth.positive?
      if pair == '/-'
        depth += 1
        clean << '  '
        index += 2
      elsif pair == '-/'
        depth -= 1
        clean << '  '
        index += 2
      else
        clean << (char == "\n" ? "\n" : ' ')
        index += 1
      end
    elsif in_string
      if char == '\\'
        clean << '  '
        index += 2
      else
        in_string = false if char == '"'
        clean << (char == "\n" ? "\n" : ' ')
        index += 1
      end
    elsif pair == '/-'
      depth = 1
      clean << '  '
      index += 2
    elsif pair == '--'
      last = source.index("\n", index) || source.length
      clean << (' ' * (last - index))
      index = last
    elsif char == '"'
      in_string = true
      clean << ' '
      index += 1
    else
      clean << char
      index += 1
    end
  end
  abort "Unclosed comment or string: #{path}" unless depth.zero? && !in_string
  clean
end

# This source gate deliberately supports one module per single-line import.
# Inspect every remaining import token, rather than silently ignoring syntax
# such as `import\n  Production.Module`, which Lean also accepts. Comments and
# strings have already been masked by lean_code; unsupported forms fail closed.
def canonical_imports(code, path)
  module_name = /[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*/
  declaration = /\A[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+(#{module_name})[ \t]*\r?\n?\z/
  code.lines.each_with_index.map do |line, index|
    next unless line.match?(/\bimport\b/)
    match = declaration.match(line)
    abort "Unsupported import syntax: #{path}:#{index + 1}; use one single-line `import Module.Name` per module" unless match
    match[1]
  end.compact
end

Dir.chdir(File.expand_path('..', __dir__)) do
  required = Set.new
  pending = ['OSReconstruction']
  admissions = 0
  axioms = 0
  until pending.empty?
    mod = pending.pop
    next unless required.add?(mod)
    path = mod.tr('.', '/') + '.lean'
    abort "Missing source: #{path}" unless File.file?(path) && !File.symlink?(path)
    code = lean_code(path)
    admissions += code.scan(/\b(?:sorry|admit|sorryAx)\b/).size
    axioms += code.scan(/\baxiom\b/).size
    imports = canonical_imports(code, path)
    abort "Production imports the Comparator challenge: #{path}" if imports.include?('Challenge')
    pending.concat(imports.select { |name| name == 'OSReconstruction' || name.start_with?('OSReconstruction.') })
  end
  actual = (Dir.glob('OSReconstruction/**/*.lean') + ['OSReconstruction.lean']).to_set
  expected = required.map { |mod| mod.tr('.', '/') + '.lean' }.to_set
  abort "Sources outside import closure: #{(actual - expected).to_a.join(', ')}" unless actual == expected
  puts "Source census: #{admissions} direct admissions; #{axioms} explicit project axioms."
  abort 'Source census failed' unless admissions.zero? && axioms.zero?
  puts "PASS: #{required.size} production modules, exactly the source import closure."

  # The standard Comparator checks the exported proof. These source checks keep
  # its human-readable boundary independent and its deliberate holes confined.
  boundary = 'verification/comparator'
  config = JSON.parse(File.read("#{boundary}/comparator.json"))
  targets = %w[OSReconstructionAudit.e_to_r OSReconstructionAudit.e_to_r_osii OSReconstructionAudit.r_to_e]
  abort 'Unexpected Comparator targets' unless config['theorem_names'] == targets
  abort 'Comparator definition holes are not permitted' unless (config['definition_names'] || []).empty?
  allowed = %w[propext Classical.choice Quot.sound].to_set
  abort 'Unexpected Comparator axiom whitelist' unless config.fetch('permitted_axioms').to_set == allowed
  abort 'Unexpected Comparator modules' unless config['challenge_module'] == 'Challenge' && config['solution_module'] == 'Solution'

  %w[Definitions Challenge Solution WightmanBridge OSBridge ReverseBridge].each do |mod|
    path = "#{boundary}/#{mod}.lean"
    abort "Missing Comparator source: #{path}" unless File.file?(path) && !File.symlink?(path)
  end
  Dir.glob("#{boundary}/**/*.lean").reject { |path| path.include?('/.lake/') }.each do |path|
    code = lean_code(path)
    holes = code.scan(/\b(?:sorry|admit|sorryAx)\b/)
    if path == "#{boundary}/Challenge.lean"
      abort 'Challenge must have exactly three theorem placeholders' unless holes == %w[sorry sorry sorry]
    else
      abort "Admission outside Challenge: #{path}" unless holes.empty?
    end
    abort "Axiom or native_decide in Comparator sources: #{path}" if code.match?(/\b(?:axiom|native_decide)\b/)
    imports = canonical_imports(code, path)
    abort "Import of Challenge: #{path}" if imports.include?('Challenge')
    if path == "#{boundary}/Definitions.lean"
      abort 'Audit definitions must import only Mathlib' unless !imports.empty? && imports.all? { |name| name == 'Mathlib' || name.start_with?('Mathlib.') }
    elsif path == "#{boundary}/Challenge.lean"
      abort 'Challenge must import only Definitions' unless imports == ['Definitions']
    end
  end
  puts 'PASS: Mathlib-only audit definitions, three isolated challenge placeholders, standard Comparator whitelist.'
end
