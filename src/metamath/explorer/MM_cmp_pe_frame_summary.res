open MM_syntax_tree
open Expln_React_common
open Expln_React_Mui
open MM_wrk_editor
open MM_react_common
open MM_context
open MM_substitution
open MM_parenCounter
open MM_proof_tree
open MM_proof_tree_dto
open Expln_React_Modal
open Local_storage_utils
open Common
open MM_cmp_user_stmt

type state = {
    frmCtx:mmContext,
    symColors:Belt_HashMapString.t<string>,
    eHyps:array<expr>,
    asrt:expr,
    descrIsExpanded:bool
}

let makeInitialState = (~preCtx:mmContext, ~frame:frame, ~typeColors:Belt_HashMapString.t<string>):state => {
    let frmCtx = createContext(~parent=preCtx, ())
    let symRename = ref(None)
    let frmVarIntToCtxInt = []
    let symColors = Belt_HashMapString.make(~hintSize=frame.numOfVars)

    let createLocalCtxVar = (~frmVarName, ~typInt):int => {
        @warning("-8")
        let [ctxVarName] = generateNewVarNames( 
            ~ctx=frmCtx, 
            ~types=[typInt], 
            ~typeToPrefix=Belt_MapString.empty, 
            ()
        )
        @warning("-8")
        let [ctxVarLabel] = generateNewLabels(
            ~ctx=frmCtx, 
            ~prefix="loc-var-", 
            ~amount=1,
            ()
        )
        frmCtx->applySingleStmt(Var({symbols:[ctxVarName]}))
        frmCtx->applySingleStmt(Floating({label:ctxVarLabel, expr:[frmCtx->ctxIntToSymExn(typInt), ctxVarName]}))
        switch symRename.contents {
            | None => {
                let map = Belt_HashMapString.make(~hintSize=frame.numOfVars)
                map->Belt_HashMapString.set(ctxVarName, frmVarName)
                symRename := Some(map)
            }
            | Some(symRename) => {
                symRename->Belt_HashMapString.set(ctxVarName, frmVarName)
            }
        }
        frmCtx->ctxSymToIntExn(ctxVarName)
    }

    for frmVarInt in 0 to frame.numOfVars-1 {
        let frmVarName = frame.frameVarToSymb[frmVarInt]
        let ctxVarInt = frmCtx->ctxSymToIntExn(frmVarName)
        let ctxVarTypInt = frmCtx->getTypeOfVarExn(ctxVarInt)
        let ctxVarName = switch frmCtx->getTokenType(frmVarName) {
            | Some(V) => {
                if (frame.varTypes[frmVarInt] == ctxVarTypInt) {
                    frmVarIntToCtxInt->Js.Array2.push(ctxVarInt)->ignore
                    frmVarName
                } else {
                    let ctxNewVarInt = createLocalCtxVar(~frmVarName, ~typInt=frame.varTypes[frmVarInt])
                    frmVarIntToCtxInt->Js.Array2.push(ctxNewVarInt)->ignore
                    frmCtx->ctxIntToSymExn(ctxNewVarInt)
                }
            }
            | _ => {
                let ctxNewVarInt = createLocalCtxVar(~frmVarName, ~typInt=frame.varTypes[frmVarInt])
                frmVarIntToCtxInt->Js.Array2.push(ctxNewVarInt)->ignore
                frmCtx->ctxIntToSymExn(ctxNewVarInt)
            }
        }
        let frmVarTypSym = frmCtx->ctxIntToSymExn(frame.varTypes[frmVarInt])
        typeColors->Belt_HashMapString.get(frmVarTypSym)->Belt.Option.forEach(color => {
            symColors->Belt_HashMapString.set(ctxVarName, color)
        })
    }

    let frameExprToCtxExpr = (frmExpr:expr):expr => {
        frmExpr->Js_array2.map(i => if (i < 0) {i} else {frmVarIntToCtxInt[i]})
    }

    {
        frmCtx,
        symColors,
        eHyps:frame.hyps->Js.Array2.filter(hyp => hyp.typ == E)->Js.Array2.map(hyp => hyp.expr->frameExprToCtxExpr),
        asrt:frame.asrt->frameExprToCtxExpr,
        descrIsExpanded:false
    }
}

type props = {
    modalRef:modalRef,
    settingsVer:int,
    preCtxVer:int,
    preCtx:mmContext,
    frame:frame,
    typeColors:Belt_HashMapString.t<string>,
    editStmtsByLeftClick:bool,
}

let propsAreSame = (a:props,b:props):bool => {
    a.settingsVer == b.settingsVer
    && a.preCtxVer == b.preCtxVer
}

let make = React.memoCustomCompareProps( ({
    modalRef,
    settingsVer,
    preCtxVer,
    preCtx,
    frame,
    typeColors,
    editStmtsByLeftClick,
}:props) =>  {
    let (state, setState) = React.useState(_ => makeInitialState(~preCtx, ~frame, ~typeColors))

    React.useEffect2(() => {
        setState(_ => makeInitialState(~preCtx, ~frame, ~typeColors))
        None
    }, (settingsVer, preCtxVer))

    React.null

}, propsAreSame)