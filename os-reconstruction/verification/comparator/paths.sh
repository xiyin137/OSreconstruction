# Resolve both sides of the sandbox boundary physically. In particular, .lake
# and existing tool checkouts may themselves be symlinks.
comparator_resolve_directory() {
  (cd "$1" && pwd -P)
}

comparator_resolve_tool_directory() {
  local directory lake_directory
  directory="$(comparator_resolve_directory "$1")" || return 1
  lake_directory="$(comparator_resolve_directory "$2")" || return 1
  case "$directory/" in
    "$lake_directory/"*)
      echo "Keep comparator tools outside the sandbox-writable project .lake directory: $directory" >&2
      return 1
      ;;
  esac
  printf '%s\n' "$directory"
}
