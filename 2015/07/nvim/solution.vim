#!/usr/bin/env -S nvim --clean -s
:i
#!/usr/bin/env stack
-- stack --resolver lts-22.13 script
import Data.Bits
rshift' = shiftR
lshift' = shiftL
and' = (.&.)
or' = (.|.)
main = print (a' :: Integer)


:r input
:'{,'}s/\(.*\) -> \(.*\)/\2 = \1/
:'{,'}s/\([a-z]\+\)/\1'/g
:'{,'}s/NOT/complement/
:'{,'}s/\<\([A-Z]\+\)\>/`\L\1'`/
:exe 'w ' . tempname()
:!chmod +x %
:let @a = system(expand('%:p'))
:exe '%s/^b\'' = .*$/b\'' = ' . trim(@a) . '/'
:w
:let @b = trim(system(expand('%:p')))
:%d
"aPj"bP
:w
