#!/usr/bin/env zsh

for eq in "==" "!="; do
    grep , input \
        | tr ',' '|' \
        | xargs --max-procs=$(nproc) -I '{}' \
            zsh -c '
                sorted=$( \
                    grep '"'"'|'"'"' input \
                        | grep -E '"'"'({})\|({})'"'"' \
                        | tr '"'"'|'"'"' '"'"' '"'"' \
                        | tsort \
                        | grep -E '"'"'{}'"'"' \
                );
                length=$(echo "$sorted" | wc -l);
                if [[
                    $(echo '"'"'{}'"'"' | tr '"'"'|'"'"' '"'"','"'"'),
                    '$eq' $(echo "$sorted" | tr '"'"'\n'"'"' '"'"','"'"')
                ]]; then
                    echo "$sorted" | head -n $(($length / 2 + 1)) | tail -n1
                fi' \
        | sed -E 's/\s+/+/g' \
        | paste -sd+ \
        | bc
done
