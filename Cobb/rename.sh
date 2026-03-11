for dir in */; do
  dir="${dir%/}"
  if [[ "$dir" == *_min_sketch ]]; then
    new_dir="${dir%_min_sketch}_max_sketch"
    cp -r "$dir" "$new_dir"
  fi
done