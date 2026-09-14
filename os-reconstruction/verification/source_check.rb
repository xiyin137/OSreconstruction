#!/usr/bin/env ruby
require 'set'

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
    imports = code.scan(/^\s*(?:(?:public|private|meta)\s+)?import[ \t]+([^\n]+)/)
                  .flat_map { |(line)| line.split }
    pending.concat(imports.select { |name| name == 'OSReconstruction' || name.start_with?('OSReconstruction.') })
  end
  actual = (Dir.glob('OSReconstruction/**/*.lean') + ['OSReconstruction.lean']).to_set
  expected = required.map { |mod| mod.tr('.', '/') + '.lean' }.to_set
  abort "Sources outside import closure: #{(actual - expected).to_a.join(', ')}" unless actual == expected
  puts "Source census: #{admissions} direct admissions; #{axioms} explicit project axioms."
  abort 'Source census failed' unless admissions.zero? && axioms.zero?
  puts "PASS: #{required.size} production modules, exactly the source import closure."
end
