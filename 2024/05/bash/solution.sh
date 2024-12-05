#!/usr/bin/env bash

for eq in "==" "!="; do grep , input | tr ',' '|' | xargs -I '{}' bash -c 'l=$(grep -E '"'"'({})\|({})'"'"' input | tr '"'"'|'"'"' '"'"' '"'"' | tsort | grep -E '"'"'{}'"'"'); n=$(echo "$l" | wc -l); if [[ $(echo '"'"'{}'"'"' | tr '"'"'|'"'"' '"'"','"'"'), '$eq' $(echo "$l" | tr '"'"'\n'"'"' '"'"','"'"') ]]; then echo "$l" | head -n $(($n / 2 + 1)) | tail -n1; fi' | sed -E 's/\s+/+/g' | paste -sd+ | bc; done
