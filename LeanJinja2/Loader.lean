import LeanJinja2.APIs

/-!
# `FileSystemLoader`: the one effectful module

Upstream's `FileSystemLoader(searchpath)` reads a template from the first
directory of the search path that has it. Here the loader reads the search
path once, in `IO`, into the pure `Loader.fileSystem` value: every file under
each directory, by its `/`-separated name relative to that directory, earlier
directories first. Rendering then never performs IO.

```lean
let env : Environment := { loader := ← FileSystemLoader "templates",
                           autoescape := selectAutoescape }
let t ← IO.ofExcept (env.getTemplate "index.html")
IO.println (← IO.ofExcept (t.render [("name", "World")]))
```
-/

namespace LeanJinja2

/-- What `FileSystemLoader` accepts: one directory or a list of them. -/
class ToSearchPath (α : Type) where
  toSearchPath : α → List String

instance : ToSearchPath String := ⟨fun s => [s]⟩
instance : ToSearchPath System.FilePath := ⟨fun p => [p.toString]⟩
instance : ToSearchPath (List String) := ⟨id⟩

/-- The `/`-separated name of `file` relative to `root`. -/
def relativeName (root file : System.FilePath) : String :=
  let r := root.normalize.components.filter (· != "")
  let f := file.normalize.components.filter (· != "")
  "/".intercalate (f.drop r.length)

/-- The template files under one directory (none if it does not exist). -/
def templatesUnder (dir : String) : IO (List (String × String)) := do
  let root : System.FilePath := dir
  if !(← root.isDir) then return []
  let paths ← root.walkDir
  let mut out : List (String × String) := []
  for p in paths do
    if !(← p.isDir) then
      match ← (IO.FS.readFile p).toBaseIO with
      | .ok src => out := out ++ [(relativeName root p, src)]
      | .error _ => pure ()
  return out

/-- `FileSystemLoader(searchpath)`: a directory or a list of directories. -/
def FileSystemLoader {α : Type} [ToSearchPath α] (searchpath : α) : IO Loader := do
  let dirs := ToSearchPath.toSearchPath searchpath
  let mut files : List (String × String) := []
  for d in dirs do
    files := files ++ (← templatesUnder d)
  return .fileSystem dirs files

end LeanJinja2
