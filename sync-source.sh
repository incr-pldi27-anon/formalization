#!/usr/bin/env bash
set -euo pipefail

# Copy only the formalization and its pinned build configuration. Review the
# resulting diff and anonymity before publishing; this script does not push.
dest=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
source_dir=${1:-"$dest/../incr2"}
source_dir=$(cd -- "$source_dir" && pwd -P)
if [[ "$source_dir" == "$dest" ]]; then
  echo 'Source and destination must differ.' >&2
  exit 1
fi

files=(lean-toolchain lakefile.toml lake-manifest.json Incr.lean)
dirs=(Incr comparator)

for file in "${files[@]}"; do
  [[ -f "$source_dir/$file" ]] || { echo "Missing source file: $file" >&2; exit 1; }
done
for dir in "${dirs[@]}"; do
  [[ -d "$source_dir/$dir" ]] || { echo "Missing source directory: $dir" >&2; exit 1; }
done
[[ -f "$source_dir/comparator/comparator.json" ]] || {
  echo 'Missing source file: comparator/comparator.json' >&2; exit 1; }

# Retired layout from the pre-rename snapshot.
rm -rf -- "$dest/Incr2"
rm -f -- "$dest/Incr2.lean"

for dir in "${dirs[@]}"; do
  mkdir -p -- "$dest/$dir"
  rsync -rmc --delete --include='*/' --include='*.lean' --exclude='*' \
    "$source_dir/$dir/" "$dest/$dir/"
done
cp -- "$source_dir/comparator/comparator.json" "$dest/comparator/comparator.json"
for file in "${files[@]}"; do
  cp -- "$source_dir/$file" "$dest/$file"
done

printf 'Snapshot updated. Review all changes and anonymity before pushing.\n'
