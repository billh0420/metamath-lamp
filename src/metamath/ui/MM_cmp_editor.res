open MM_context
open Expln_React_common
open Expln_React_Mui
open Modal
open MM_wrk_editor
open MM_wrk_settings
open MM_wrk_ctx
open MM_wrk_unify
open MM_substitution
open MM_parser
open MM_proof_tree
open MM_proof_table
open Expln_utils_promise

type userStmtLocStor = {
    id: string,

    label: string,
    typ: string,
    cont: string,
    
    jstfText: string,
}   

type editorStateLocStor = {
    varsText: string,
    disjText: string,

    nextStmtId: int,
    stmts: array<userStmtLocStor>,
}

let userStmtLocStorToUserStmt = (userStmtLocStor:userStmtLocStor):userStmt => {
    {
        id: userStmtLocStor.id,

        label: userStmtLocStor.label,
        labelEditMode: false,
        typ: userStmtTypeFromStr(userStmtLocStor.typ),
        typEditMode: false,
        cont: strToCont(userStmtLocStor.cont),
        contEditMode: false,

        jstfText: userStmtLocStor.jstfText,
        jstfEditMode: false,

        stmtErr: None,

        expr: None,
        jstf: None,
        proof: None,
        proofStatus: None,
    }
}

let createInitialEditorState = (settingsV, settings, preCtxV, preCtx, stateLocStor:option<editorStateLocStor>) => {
    {
        settingsV,
        settings,

        preCtxV,
        preCtx,
        frms: prepareFrmSubsData(preCtx),

        varsText: stateLocStor->Belt.Option.map(obj => obj.varsText)->Belt.Option.getWithDefault(""),
        varsEditMode: false,
        varsErr: None,

        disjText: stateLocStor->Belt.Option.map(obj => obj.disjText)->Belt.Option.getWithDefault(""),
        disjEditMode: false,
        disjErr: None,
        disj: Belt_MapInt.fromArray([]),

        wrkCtx: None,

        nextStmtId: stateLocStor->Belt.Option.map(obj => obj.nextStmtId)->Belt.Option.getWithDefault(0),
        stmts: 
            stateLocStor
                ->Belt.Option.map(obj => obj.stmts->Js_array2.map(userStmtLocStorToUserStmt))
                ->Belt.Option.getWithDefault([]),
        checkedStmtIds: [],
    }
}

let editorStateToEditorStateLocStor = (state:editorState):editorStateLocStor => {
    {
        varsText: state.varsText,
        disjText: state.disjText,
        nextStmtId: state.nextStmtId,
        stmts: state.stmts->Js_array2.map(stmt => {
            {
                id: stmt.id,
                label: stmt.label,
                typ: (stmt.typ :> string),
                cont: contToStr(stmt.cont),
                jstfText: stmt.jstfText,
            }
        }),
    }
}

let editorSaveStateToLocStor = (state:editorState, key:string):unit => {
    Dom_storage2.localStorage->Dom_storage2.setItem(key, Expln_utils_common.stringify(state->editorStateToEditorStateLocStor))
}

let readEditorStateFromLocStor = (key:string):option<editorStateLocStor> => {
    switch Dom_storage2.localStorage->Dom_storage2.getItem(key) {
        | None => None
        | Some(stateLocStorStr) => {
            open Expln_utils_jsonParse
            let parseResult = parseObj(stateLocStorStr, d=>{
                {
                    varsText: d->strOpt("varsText")->Belt_Option.getWithDefault(""),
                    disjText: d->strOpt("disjText")->Belt_Option.getWithDefault(""),
                    nextStmtId: d->int("nextStmtId"),
                    stmts: d->arr("stmts", d=>{
                        {
                            id: d->str("id"),
                            label: d->str("label"),
                            typ: d->str("typ"),
                            cont: d->str("cont"),
                            jstfText: d->str("jstfText")
                        }
                    })
                }
            })
            switch parseResult {
                | Error(_) => None
                | Ok(res) => Some(res)
            }
        }
    }
}

let rndIconButton = (~icon:reElem, ~onClick:unit=>unit, ~active:bool, ~title:option<string>=?, ()) => {
    <span ?title>
        <IconButton disabled={!active} onClick={_ => onClick()} color="primary"> icon </IconButton>
    </span>
}

let stateLocStorKey = "editor-state"

let lastUsedAsrtSearchTypLocStorKey = "search-asrt-typ"

let saveLastUsedTyp = (ctx,typInt) => {
    switch ctx->ctxIntToSym(typInt) {
        | None => ()
        | Some(typStr) =>
            Dom_storage2.localStorage->Dom_storage2.setItem(lastUsedAsrtSearchTypLocStorKey, typStr)
    }
}

let getLastUsedTyp = (ctx) => {
    switch Dom_storage2.localStorage->Dom_storage2.getItem(lastUsedAsrtSearchTypLocStorKey) {
        | None => None
        | Some(typStr) => ctx->ctxSymToInt(typStr)
    }
}

@react.component
let make = (~modalRef:modalRef, ~settingsV:int, ~settings:settings, ~preCtxV:int, ~preCtx:mmContext, ~top:int) => {
    let (state, setStatePriv) = React.useState(_ => createInitialEditorState(
        settingsV, settings, preCtxV, preCtx, readEditorStateFromLocStor(stateLocStorKey)
    ))

    let setState = (update:editorState=>editorState) => {
        setStatePriv(st => {
            let st = update(st)
            let st = prepareEditorForUnification(st)
            let st = if (st.wrkCtx->Belt_Option.isSome) {
                removeUnusedVars(st)
            } else {
                st
            }
            editorSaveStateToLocStor(st, stateLocStorKey)
            st
        })
    }

    let actSettingsUpdated = (settingsV, settings) => {
        setState(setSettings(_, settingsV, settings))
    }

    React.useEffect1(() => {
        actSettingsUpdated(settingsV, settings)
        None
    }, [settingsV])

    let actPreCtxUpdated = (preCtxV, preCtx) => {
        setState(setPreCtx(_, preCtxV, preCtx))
    }

    React.useEffect1(() => {
        actPreCtxUpdated(preCtxV, preCtx)
        None
    }, [preCtxV])

    let thereAreSyntaxErrors = editorStateHasErrors(state)
    let mainCheckboxState = {
        let atLeastOneStmtIsChecked = state.checkedStmtIds->Js.Array2.length != 0
        let atLeastOneStmtIsNotChecked = state.stmts->Js.Array2.length != state.checkedStmtIds->Js.Array2.length
        if (atLeastOneStmtIsChecked && atLeastOneStmtIsNotChecked) {
            None
        } else if (atLeastOneStmtIsChecked && !atLeastOneStmtIsNotChecked) {
            Some(true)
        } else {
            Some(false)
        }
    }

    let editIsActive = 
        state.varsEditMode || state.disjEditMode ||
        state.stmts->Js.Array2.some(stmt => stmt.labelEditMode || stmt.typEditMode || stmt.contEditMode || stmt.jstfEditMode )

    let actAddNewStmt = () => setState(st => {
        let (st, _) = addNewStmt(st)
        st
    })
    let actDeleteCheckedStmts = () => {
        openModal(modalRef, _ => React.null)->promiseMap(modalId => {
            updateModal(modalRef, modalId, () => {
                <Paper style=ReactDOM.Style.make(~padding="10px", ())>
                    <Col spacing=1.>
                        {React.string("Delete selected statements?")}
                        <Row>
                            <Button onClick={_=>closeModal(modalRef, modalId)}> {React.string("Cancel")} </Button>
                            <Button
                                onClick={_=>{
                                    closeModal(modalRef, modalId)
                                    setState(deleteCheckedStmts)
                                }}
                                variant=#contained
                            > 
                                {React.string("Delete")} 
                            </Button>
                        </Row>
                    </Col>
                </Paper>
            })
        })->ignore
    }
    let actToggleStmtChecked = id => {
        setStatePriv(st => {
            let st = toggleStmtChecked(st,id)
            editorSaveStateToLocStor(st, stateLocStorKey)
            st
        })
    }
    let actToggleMainCheckbox = () => {
        let action = switch mainCheckboxState {
            | Some(true) | None => uncheckAllStmts
            | Some(false) => checkAllStmts
        }
        setStatePriv(st => {
            let st = action(st)
            editorSaveStateToLocStor(st, stateLocStorKey)
            st
        })
    }
    let actMoveCheckedStmtsUp = () => setState(moveCheckedStmts(_, true))
    let actMoveCheckedStmtsDown = () => setState(moveCheckedStmts(_, false))
    let actDuplicateStmt = () => setState(st => {
        let st = duplicateCheckedStmt(st)
        let st = uncheckAllStmts(st)
        st
    })
    let actBeginEdit0 = (setter:editorState=>editorState) => {
        if (!editIsActive) {
            setState(setter)
        }
    }
    let actBeginEdit = (setter:(editorState,string)=>editorState, stmtId:string) => {
        if (!editIsActive) {
            setState(setter(_,stmtId))
        }
    }
    let actCompleteEdit = (setter:editorState=>editorState) => {
        setState(setter)
    }

    let actAsrtSearchResultsSelected = selectedResults => {
        setState(st => selectedResults->Js_array2.reduce( addAsrtSearchResult, st ))
    }

    let actWrkSubsSelected = wrkSubs => {
        setState(st => st->applySubstitutionForEditor(wrkSubs))
    }

    let actSearchAsrt = () => {
        switch state.wrkCtx {
            | None => ()
            | Some(wrkCtx) => {
                openModal(modalRef, _ => React.null)->promiseMap(modalId => {
                    updateModal(modalRef, modalId, () => {
                        <MM_cmp_search_asrt
                            modalRef
                            preCtxVer=state.preCtxV
                            preCtx=state.preCtx
                            parenStr=state.settings.parens
                            varsText=state.varsText
                            disjText=state.disjText
                            hyps={
                                state.stmts
                                    ->Js_array2.filter(stmt => stmt.typ == #e)
                                    ->Js_array2.map(stmt => {id:stmt.id, label:stmt.label, text:stmt.cont->contToStr})
                            }
                            wrkCtx
                            frms=state.frms
                            initialTyp={getLastUsedTyp(state.preCtx)}
                            onTypChange={saveLastUsedTyp(state.preCtx, _)}
                            onCanceled={()=>closeModal(modalRef, modalId)}
                            onResultsSelected={selectedResults=>{
                                closeModal(modalRef, modalId)
                                actAsrtSearchResultsSelected(selectedResults)
                            }}
                        />
                    })
                })->ignore
            }
        }
    }

    let actSubstitute = () => {
        switch state.wrkCtx {
            | None => ()
            | Some(wrkCtx) => {
                openModal(modalRef, _ => React.null)->promiseMap(modalId => {
                    updateModal(modalRef, modalId, () => {
                        <MM_cmp_substitution
                            editorState=state
                            wrkCtx
                            onCanceled={()=>closeModal(modalRef, modalId)}
                            onSubstitutionSelected={wrkSubs=>{
                                closeModal(modalRef, modalId)
                                actWrkSubsSelected(wrkSubs)
                            }}
                        />
                    })
                })->ignore
            }
        }
    }

    let actUnifyAllResultsAreReady = proofTreeDto => {
        setStatePriv(st => {
            let st = applyUnifyAllResults(st, proofTreeDto)
            editorSaveStateToLocStor(st, stateLocStorKey)
            st
        })
    }

    let actUnifyAll = () => {
        switch state.wrkCtx {
            | None => ()
            | Some(_) => {
                openModal(modalRef, () => rndProgress(~text="Unifying", ~pct=0.))->promiseMap(modalId => {
                    unify(
                        ~preCtxVer=state.preCtxV,
                        ~preCtx=state.preCtx,
                        ~parenStr=state.settings.parens,
                        ~varsText=state.varsText,
                        ~disjText=state.disjText,
                        ~hyps={
                            state.stmts
                                ->Js_array2.filter(stmt => stmt.typ == #e)
                                ->Js_array2.map(stmt => {id:stmt.id, label:stmt.label, text:stmt.cont->contToStr})
                        },
                        ~stmts={
                            state.stmts
                                ->Js_array2.filter(stmt => stmt.typ == #p)
                                ->Js_array2.map(stmt => {
                                    {
                                        label:Some(stmt.label),
                                        expr:
                                            switch stmt.expr {
                                                | None => raise(MmException({msg:`Expr must be set for all statements before unification.`}))
                                                | Some(expr) => expr
                                            },
                                        justification: stmt.jstf,
                                    }
                                })
                        },
                        ~onProgress = pct => updateModal(modalRef, modalId, () => rndProgress(~text="Unifying", ~pct))
                    )->promiseMap(proofTreeDto => {
                        closeModal(modalRef, modalId)
                        actUnifyAllResultsAreReady(proofTreeDto)
                    })
                })->ignore
            }
        }
    }

    let splitIntoChunks = (str, chunkMaxSize): array<string> => {
        let len = str->Js_string2.length
        if (len <= chunkMaxSize) {
            [str]
        } else {
            let res = []
            let numberOfChunks = Js.Math.ceil_int(len->Belt_Int.toFloat /. chunkMaxSize->Belt_Int.toFloat)
            for i in 1 to numberOfChunks {
                let begin = (i-1)*chunkMaxSize
                res->Js_array2.push(str->Js_string2.substrAtMost(~from=begin, ~length=chunkMaxSize))->ignore
            }
            res
        }
    }

    let proofToText = (ctx:mmContext,stmt:userStmt,proof:proof):string => {
        switch proof {
            | Compressed({labels, compressedProofBlock}) => {
                let blk = splitIntoChunks(compressedProofBlock, 50)->Js_array2.joinWith(" ")
                let asrt = `${stmt.label} $p ${stmt.cont->contToStr} $= ( ${labels->Js_array2.joinWith(" ")} ) ${blk} $.`
                let localVars = ctx->getLocalVars
                let localDisj = ctx->getLocalDisj
                let localHyps = ctx->getLocalHyps
                let blockIsRequired = localHyps->Js.Array2.length > 0 || !(localDisj->disjIsEmpty)
                let result = []
                if (blockIsRequired) {
                    result->Js.Array2.push("${")->ignore
                }
                if (localVars->Js.Array2.length > 0) {
                    result->Js.Array2.push("$v " ++ localVars->Js.Array2.joinWith(" ") ++ " $.")->ignore
                }
                localDisj->disjForEachArr(vars => {
                    result->Js.Array2.push("$d " ++ ctx->ctxIntsToStrExn(vars) ++ " $.")->ignore
                })
                localHyps->Js.Array2.forEach(hyp => {
                    let hypTypStr = if (hyp.typ == F) {
                        " $f "
                    } else {
                        " $e "
                    }
                    result->Js.Array2.push(hyp.label ++ hypTypStr ++ ctx->ctxIntsToStrExn(hyp.expr) ++ " $.")->ignore
                })
                result->Js.Array2.push(asrt)->ignore
                if (blockIsRequired) {
                    result->Js.Array2.push("$}")->ignore
                }
                result->Js.Array2.joinWith("\r\n")
            }
            | _ => "Error: only compressed proofs are supported."
        }
    }

    let rndExportedProof = (proofStr, modalId) => {
        <Paper style=ReactDOM.Style.make( ~padding="10px", () ) >
            <Col>
                <pre style=ReactDOM.Style.make(~overflowWrap="break-word", ~whiteSpace="pre-wrap", ())>{React.string(proofStr)}</pre>
                <Button onClick={_=>closeModal(modalRef, modalId)}> {React.string("Close")} </Button>
            </Col>
        </Paper>
    }

    let actExportProof = (stmtId) => {
        switch state.wrkCtx {
            | None => ()
            | Some(wrkCtx) => {
                switch state.stmts->Js.Array2.find(stmt => stmt.id == stmtId) {
                    | None => ()
                    | Some(stmt) => {
                        switch stmt.proof {
                            | None => ()
                            | Some(proofNode) => {
                                let proofTable = proofTreeCreateProofTable(proofNode)
                                proofTablePrint(wrkCtx, proofTable, "exported-proof")
                                let proof = createProof(wrkCtx, proofTable, proofTable->Js_array2.length-1)
                                openModal(modalRef, () => React.null)->promiseMap(modalId => {
                                    updateModal(modalRef, modalId, () => {
                                        rndExportedProof(proofToText(wrkCtx,stmt,proof), modalId)
                                    })
                                })->ignore
                            }
                        }
                    }
                }
            }
        }
    }

    let rndError = msgOpt => {
        switch msgOpt {
            | None => React.null
            | Some(msg) => <pre style=ReactDOM.Style.make(~color="red", ())>{React.string(msg)}</pre>
        }
    }

    let rndButtons = () => {
        let generalModificationActionIsEnabled =
            !editIsActive
            && !thereAreSyntaxErrors
        let atLeastOneStmtIsSelected = mainCheckboxState->Belt_Option.getWithDefault(true)
        <Paper>
            <Row>
                <Checkbox
                    disabled=editIsActive
                    indeterminate={mainCheckboxState->Belt_Option.isNone}
                    checked={mainCheckboxState->Belt_Option.getWithDefault(false)}
                    onChange={_ => actToggleMainCheckbox()}
                />
                {rndIconButton(~icon=<Icons2.ArrowDownward/>, ~onClick=actMoveCheckedStmtsDown, ~active= !editIsActive && canMoveCheckedStmts(state,false),
                    ~title="Move selected statements down", ())}
                {rndIconButton(~icon=<Icons2.ArrowUpward/>, ~onClick=actMoveCheckedStmtsUp, ~active= !editIsActive && canMoveCheckedStmts(state,true),
                    ~title="Move selected statements up", ())}
                {rndIconButton(~icon=<Icons2.Add/>, ~onClick=actAddNewStmt, ~active= !editIsActive, 
                    ~title="Add new statement (and place before selected statements if any)", ())}
                {rndIconButton(~icon=<Icons2.DeleteForever/>, ~onClick=actDeleteCheckedStmts, 
                    ~active= !editIsActive && atLeastOneStmtIsSelected, ~title="Delete selected statements", ()
                )}
                {rndIconButton(~icon=<Icons2.ControlPointDuplicate/>, ~onClick=actDuplicateStmt, ~active= !editIsActive && isSingleStmtChecked(state), 
                    ~title="Duplicate selected statement", ())}
                { 
                    rndIconButton(~icon=<Icons2.Search/>, ~onClick=actSearchAsrt, 
                        ~active=generalModificationActionIsEnabled && state.frms->Belt_MapString.size > 0,
                        ~title="Add new statements from existing assertions (and place before selected statements if any)", ()
                    ) 
                }
                { rndIconButton(~icon=<Icons2.TextRotationNone/>, ~onClick=actSubstitute, ~active=generalModificationActionIsEnabled,
                    ~title="Apply a substitution to all statements", () ) }
                { 
                    rndIconButton(~icon=<Icons2.Hub/>, ~onClick=actUnifyAll, 
                        ~active=generalModificationActionIsEnabled 
                                    && !atLeastOneStmtIsSelected
                                    && state.stmts->Js_array2.length > 0, 
                        ~title="Unify all statements", () )
                }
            </Row>
        </Paper>
    }

    let rndStmt = (stmt:userStmt) => {
        <tr key=stmt.id >
            <td style=ReactDOM.Style.make(~verticalAlign="top", ())>
                <Checkbox
                    disabled=editIsActive
                    checked={state->isStmtChecked(stmt.id)}
                    onChange={_ => actToggleStmtChecked(stmt.id)}
                />
            </td>
            <td>
                <MM_cmp_user_stmt
                    stmt

                    onLabelEditRequested={() => actBeginEdit(setLabelEditMode,stmt.id)}
                    onLabelEditDone={newLabel => actCompleteEdit(completeLabelEditMode(_,stmt.id,newLabel))}

                    onTypEditRequested={() => actBeginEdit(setTypEditMode,stmt.id)}
                    onTypEditDone={newTyp => actCompleteEdit(completeTypEditMode(_,stmt.id,newTyp))}

                    onContEditRequested={() => actBeginEdit(setContEditMode,stmt.id)}
                    onContEditDone={newCont => actCompleteEdit(completeContEditMode(_,stmt.id,newCont))}
                    
                    onJstfEditRequested={() => actBeginEdit(setJstfEditMode,stmt.id)}
                    onJstfEditDone={newJstf => actCompleteEdit(completeJstfEditMode(_,stmt.id,newJstf))}

                    onGenerateProof={()=>actExportProof(stmt.id)}
                />
                {rndError(stmt.stmtErr)}
            </td>
        </tr>
    }

    let rndVars = () => {
        <Row alignItems=#"flex-start" spacing=1. style=ReactDOM.Style.make(~marginLeft="7px", ~marginTop="7px", ())>
            {React.string("Variables")}
            <Col>
                <MM_cmp_multiline_text
                    text=state.varsText
                    editMode=state.varsEditMode
                    onEditRequested={() => actBeginEdit0(setVarsEditMode)}
                    onEditDone={newText => actCompleteEdit(completeVarsEditMode(_,newText))}
                />
                {rndError(state.varsErr)}
            </Col>
        </Row>
    }

    let rndDisj = () => {
        <Row alignItems=#"flex-start" spacing=1. style=ReactDOM.Style.make(~marginLeft="7px", ~marginTop="7px", ())>
            {React.string("Disjoints")}
            <Col>
                <MM_cmp_multiline_text
                    text=state.disjText
                    editMode=state.disjEditMode
                    onEditRequested={() => actBeginEdit0(setDisjEditMode)}
                    onEditDone={newText => actCompleteEdit(completeDisjEditMode(_,newText))}
                />
                {rndError(state.disjErr)}
            </Col>
        </Row>
    }

    let rndStmts = () => {
        <table>
            <tbody>
                { state.stmts->Js_array2.map(rndStmt)->React.array }
            </tbody>
        </table>
    }

    <ContentWithStickyHeader
        top
        header={rndButtons()}
        content={_ => {
            <Col>
                {rndVars()}
                {rndDisj()}
                {rndStmts()}
            </Col>
        }}
    />
}