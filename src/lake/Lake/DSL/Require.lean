/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Parser.Command
import Lake.Config.Dependency
import Lake.DSL.Extensions
import Lake.DSL.DeclUtil

namespace Lake.DSL
open Lean Parser Command

syntax fromPath :=
  term

syntax fromGit :=
  &" git " term:max ("@" term:max)? ("/" term)?

syntax depSpec :=
  ident " from " (fromGit <|> fromPath) (" with " term)?

def expandDepSpec (stx : TSyntax ``depSpec) (doc? : Option DocComment) : MacroM Command := do
  let depTy := mkCIdent ``Dependency
  match stx with
  | `(depSpec| $name:ident from git $url $[@ $rev?]? $[/ $path?]? $[with $opts?]?) =>
    let rev ← match rev? with | some rev => `(some $rev) | none => `(none)
    let path ← match path? with | some path => `(some $path) | none => `(none)
    let opts := opts?.getD <| ← `({})
    `($[$doc?:docComment]? @[package_dep] def $name : $depTy := {
      name := $(quote name.getId),
      src := Source.git $url $rev $path,
      opts := $opts
    })
  | `(depSpec| $name:ident from $path:term $[with $opts?]?) => do
    let opts := opts?.getD <| ← `({})
    `($[$doc?:docComment]? @[package_dep] def $name : $depTy := {
      name :=  $(quote name.getId),
      src := Source.path $path,
      opts := $opts
    })
  | _ => Macro.throwErrorAt stx "ill-formed require syntax"

/--
Adds a new package dependency to the workspace. Has two forms:

```lean
require foo from "path"/"to"/"local"/"package" with NameMap.empty
require bar from git "url.git"@"rev"/"optional"/"path-to"/"dir-with-pkg"
```

Either form supports the optional `with` clause.
The `@"rev"` and `/"path"/"dir"` parts of the git form of `require`
are optional.

The elements of both the `from` and `with` clauses are proper terms so
normal computation is supported within them (though parentheses made be
required to disambiguate the syntax).
-/
scoped macro (name := requireDecl)
doc?:(docComment)? kw:"require " spec:depSpec : command => withRef kw do
  expandDepSpec spec doc?

@[inherit_doc requireDecl] abbrev RequireDecl := TSyntax ``requireDecl

instance : Coe RequireDecl Command where
  coe x := ⟨x.raw⟩
