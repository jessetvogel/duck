import Lake

open Lake DSL

package duck

@[defaultTarget]
lean_lib Duck

require aesop from git "https://github.com/JLimperg/aesop"
