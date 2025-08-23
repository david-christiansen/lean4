/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/

module

prelude
public import Lean.Environment
public import Lean.Exception
public import Lean.Log
public import Lean.DocString.Extension
public import Lean.DocString.Links
public import Lean.Parser.Types
-- Sebastian U: Add `public` to make the build go through
import Lean.DocString.Parser
public import Lean.ResolveName

public section

set_option linter.missingDocs true

namespace Lean

variable [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m] [MonadLiftT IO m]

/--
Validates all links to the Lean reference manual in `docstring`.

This is intended to be used before saving a docstring that is later subject to rewriting with
`rewriteManualLinks`.
-/
def validateDocComment
    (docstring : TSyntax `Lean.Parser.Command.docComment) :
    m Unit := do
  let str := docstring.getDocString
  let pos? := docstring.raw[1].getHeadInfo? >>= (·.getPos?)

  let (errs, out) ← (rewriteManualLinksCore str : IO _)

  for (⟨start, stop⟩, err) in errs do
    -- Report errors at their actual location if possible
    if let some pos := pos? then
      let urlStx : Syntax := .atom (.synthetic (pos + start) (pos + stop)) (str.extract start stop)
      logErrorAt urlStx err
    else
      logError err

variable [MonadEnv m] [MonadError m] [MonadResolveName m]


open Parser in
def versoDocString
    (declName : Name) (docComment : TSyntax `Lean.Parser.Command.docComment) :
    m (Array (Doc.Block Empty Empty)) := do
  let text ← getFileMap
  -- TODO fallback to string version without nice interactivity
  let some startPos := docComment.raw[0].getTailPos? (canonicalOnly := true)
    | throwErrorAt docComment m!"Documentation comment has no source location, cannot parse"
  let some endPos := docComment.raw[1].getPos? (canonicalOnly := true)
    | throwErrorAt docComment m!"Documentation comment has no source location, cannot parse"
  -- Skip trailing `-/`
  let endPos := text.source.prev <| text.source.prev endPos
  let endPos := if endPos ≤ text.source.endPos then endPos else text.source.endPos
  have endPos_valid : endPos ≤ text.source.endPos := by
    unfold endPos
    split <;> simp [*]

  let env ← getEnv
  let ictx : InputContext :=
    .mk text.source (← getFileName) (fileMap := text)
      (endPos := endPos) (endPos_valid := endPos_valid)
  let pmctx : ParserModuleContext := {
    env,
    options := ← getOptions,
    currNamespace := (← getCurrNamespace),
    openDecls := (← getOpenDecls)
  }
  let s := mkParserState text.source |>.setPos startPos
  -- TODO parse one block at a time for error recovery purposes
  let s := Doc.Parser.blocks {} |>.run ictx pmctx (getTokenTable env) s
  panic! "Don't run me!"
  if !s.allErrors.isEmpty then
    for (pos, _, err) in s.allErrors do
      logMessage {
        fileName := (← getFileName),
        pos := text.toPosition pos,
        -- TODO end position
        data := err.toString
      }
    return #[]
  else
    let stx := s.stxStack.back
    return #[.code s!"{stx}"]

/--
Adds a docstring to the environment, validating documentation links.
-/
def addDocString (declName : Name) (docComment : TSyntax `Lean.Parser.Command.docComment) : m Unit := do
  unless (← getEnv).getModuleIdxFor? declName |>.isNone do
    throwError s!"invalid doc string, declaration '{declName}' is in an imported module"
  if let some true := doc.verso.get? (← getOptions) then
    let doc ← versoDocString declName docComment
    modifyEnv fun env => docStringExt.insert env declName (.verso doc)
  else
    validateDocComment docComment
    let docString : String ← getDocStringText docComment
    modifyEnv fun env => docStringExt.insert env declName (.markdown docString.removeLeadingSpaces)

/--
Adds a docstring to the environment, validating documentation links.
-/
def addDocString' (declName : Name) (docString? : Option (TSyntax `Lean.Parser.Command.docComment)) : m Unit :=
  match docString? with
  | some docString => addDocString declName docString
  | none => return ()
