open Expln_utils_common
open MM_parenCounter
open MM_context
open MM_unification_debug

type contunieInstruction = Continue | Stop

type constParts = {
    length: int,
    begins: array<int>,
    ends: array<int>,
    remainingMinLength: array<int>,
}

type varGroup = {
    leftConstPartIdx:int,
    frmExpr:expr,
    varsBeginIdx:int,
    numOfVars:int,
    mutable exprBeginIdx:int,
    mutable exprEndIdx:int
}

type workVars = {
    maxVar:int,
    newVars: array<int>,
    newVarTypes: array<int>,
}

type subs = {
    size: int,
    begins: array<int>,
    ends: array<int>,
    exprs: array<expr>,
    isDefined: array<bool>,
}

type frmSubsData = {
    frame: frame,
    hypsE: array<hypothesis>,
    numOfHypsE:int,
    frmConstParts:array<constParts>,
    constParts:array<constParts>,
    varGroups:array<array<varGroup>>,
    subs:subs,
}

let subsClone = subs => {
    {
        size: subs.size,
        begins: subs.begins->Js.Array2.copy,
        ends: subs.ends->Js.Array2.copy,
        exprs: subs.exprs->Js.Array2.copy,
        isDefined: subs.isDefined->Js.Array2.copy,
    }
}

let subsEq = (a:subs, b:subs):bool => {
    if (a.size == b.size && a.isDefined->Js_array2.every(b => b) && b.isDefined->Js_array2.every(b => b)) {
        let res = ref(true)
        let v = ref(0)
        while (res.contents && v.contents < a.size) {
            let aExpr = a.exprs->Js_array2.unsafe_get(v.contents)
            let aBegin = a.begins->Js_array2.unsafe_get(v.contents)
            let aEnd = a.ends->Js_array2.unsafe_get(v.contents)
            let aExprLen = aEnd - aBegin + 1
            let bExpr = b.exprs->Js_array2.unsafe_get(v.contents)
            let bBegin = b.begins->Js_array2.unsafe_get(v.contents)
            let bEnd = b.ends->Js_array2.unsafe_get(v.contents)
            let bExprLen = bEnd - bBegin + 1
            if (aExprLen == bExprLen) {
                let ai = ref(aBegin)
                let bi = ref(bBegin)
                while (res.contents && ai.contents <= aEnd) {
                    res.contents = aExpr->Js_array2.unsafe_get(ai.contents) == bExpr->Js_array2.unsafe_get(bi.contents)
                    ai.contents = ai.contents + 1
                    bi.contents = bi.contents + 1
                }
            } else {
                res.contents = false
            }
            v.contents = v.contents + 1
        }
        res.contents
    } else {
        false
    }
}

let subsHash = (subs:subs):int => {
    if (subs.isDefined->Js_array2.every(b => b)) {
        let hash = ref(0)
        let v = ref(0)
        while (v.contents < subs.size) {
            hash.contents = Expln_utils_common.hash2(
                hash.contents,
                Expln_utils_common.hashArrIntFromTo(
                    subs.exprs->Js_array2.unsafe_get(v.contents),
                    subs.begins->Js_array2.unsafe_get(v.contents),
                    subs.ends->Js_array2.unsafe_get(v.contents),
                )
            )
            v.contents = v.contents + 1
        }
        hash.contents
    } else {
        0
    }
}

let lengthOfGap = (leftConstPartIdx:int, constParts:array<array<int>>, exprLength:int):int => {
    if (leftConstPartIdx < 0) {
        constParts->Js_array2.unsafe_get(0)->Js_array2.unsafe_get(0)
    } else if (leftConstPartIdx < constParts->Js_array2.length - 1) {
        constParts->Js_array2.unsafe_get(leftConstPartIdx+1)->Js_array2.unsafe_get(0) - constParts->Js_array2.unsafe_get(leftConstPartIdx)->Js_array2.unsafe_get(1) - 1
    } else {
        exprLength - constParts->Js_array2.unsafe_get(leftConstPartIdx)->Js_array2.unsafe_get(1) - 1
    }
}

let lengthOfGap2 = (leftConstPartIdx:int, constParts:constParts, exprLength:int):int => {
    if (leftConstPartIdx < 0) {
        constParts.begins->Js_array2.unsafe_get(0)
    } else if (leftConstPartIdx < constParts.length - 1) {
        constParts.begins->Js_array2.unsafe_get(leftConstPartIdx+1) - constParts.ends->Js_array2.unsafe_get(leftConstPartIdx) - 1
    } else {
        exprLength - constParts.ends->Js_array2.unsafe_get(leftConstPartIdx) - 1
    }
}

let createConstParts = expr => {
    let constParts = []
    for i in 0 to expr->Js_array2.length-1 {
        let constPartsLength = constParts->Js_array2.length
        if (expr->Js_array2.unsafe_get(i) < 0) {
            if (constPartsLength == 0 || constParts->Js_array2.unsafe_get(constPartsLength-1)->Js_array2.unsafe_get(1) >= 0) {
                constParts->Js_array2.push([i,-1])->ignore
            }
        } else if (constPartsLength > 0 && constParts->Js_array2.unsafe_get(constPartsLength-1)->Js_array2.unsafe_get(1) < 0) {
            constParts->Js_array2.unsafe_get(constPartsLength-1)->Js_array2.unsafe_set(1, i-1)
        }
    }
    let constPartsLength = constParts->Js_array2.length
    let exprLength = expr->Js_array2.length
    if (constPartsLength > 0 && constParts->Js_array2.unsafe_get(constPartsLength-1)->Js_array2.unsafe_get(1) < 0) {
        constParts->Js_array2.unsafe_get(constPartsLength-1)->Js_array2.unsafe_set(1, exprLength-1)
    }
    let result = {
        length: constPartsLength,
        begins: createArray(constPartsLength),
        ends: createArray(constPartsLength),
        remainingMinLength: createArray(constPartsLength)
    }
    let remainingMinLength = ref(0)
    for i in constPartsLength-1 downto 0 {
        result.begins->Js_array2.unsafe_set(i, constParts->Js_array2.unsafe_get(i)->Js_array2.unsafe_get(0))
        result.ends->Js_array2.unsafe_set(i, constParts->Js_array2.unsafe_get(i)->Js_array2.unsafe_get(1))
        remainingMinLength.contents = remainingMinLength.contents + (result.ends->Js_array2.unsafe_get(i) - result.begins->Js_array2.unsafe_get(i) + 1) + lengthOfGap(i, constParts, exprLength)
        result.remainingMinLength->Js_array2.unsafe_set(i, remainingMinLength.contents)
    }
    result
}

let createMatchingConstParts = constParts => {
    {
        length: constParts.length,
        begins: createArray(constParts.length),
        ends: createArray(constParts.length),
        remainingMinLength: []
    }
}

let rec iterateConstParts = (
    ~frmExpr:expr, 
    ~expr:expr, 
    ~frmConstParts:constParts, 
    ~constParts:constParts, 
    ~idxToMatch:int, 
    ~parenCnt:parenCnt,
    ~consumer:constParts => contunieInstruction
):contunieInstruction => {
    let invokeNext = ():contunieInstruction => {
        iterateConstParts(
            ~frmExpr, 
            ~expr, 
            ~frmConstParts, 
            ~constParts, 
            ~idxToMatch=idxToMatch+1, 
            ~parenCnt,
            ~consumer
        )
    }

    let exprLen = expr->Js_array2.length
    let frmExprLen = frmExpr->Js_array2.length

    if (exprLen < frmExprLen) {
        Continue
    } else if (idxToMatch == frmConstParts.length) {
        if (frmConstParts.length > 0 && constParts.ends->Js_array2.unsafe_get(idxToMatch-1) != exprLen-1) {
            if (frmConstParts.ends->Js_array2.unsafe_get(idxToMatch-1) == frmExprLen-1) {
                Continue
            } else {
                let frmRemainingGapLength = lengthOfGap2(idxToMatch-1, frmConstParts, frmExprLen)
                let remainingGapLength = lengthOfGap2(idxToMatch-1, constParts, exprLen)
                if (remainingGapLength < frmRemainingGapLength) {
                    Continue
                } else {
                    parenCnt->parenCntReset
                    let pState = ref(Balanced)
                    let i = ref(constParts.ends->Js_array2.unsafe_get(idxToMatch-1)+1)
                    while (i.contents < exprLen && pState.contents != Failed) {
                        pState.contents = parenCnt->parenCntPut(expr->Js_array2.unsafe_get(i.contents))
                        i.contents = i.contents + 1
                    }
                    if (pState.contents == Balanced) {
                        consumer(constParts)
                    } else {
                        Continue
                    }
                }
            }
        } else {
            consumer(constParts)
        }
    } else if (idxToMatch == 0 && frmConstParts.begins->Js_array2.unsafe_get(0) == 0) {
        if (exprLen-1 < frmConstParts.ends->Js_array2.unsafe_get(0)) {
            Continue
        } else {
            let res = ref(None)
            let maxI = frmConstParts.ends->Js_array2.unsafe_get(0)
            let i = ref(0)
            while (res.contents->Belt_Option.isNone && i.contents <= maxI) {
                if (frmExpr->Js_array2.unsafe_get(i.contents) != expr->Js_array2.unsafe_get(i.contents)) {
                    res.contents = Some(Continue)
                }
                i.contents = i.contents + 1
            }
            switch res.contents {
                | Some(instr) => instr
                | None => {
                    constParts.begins->Js_array2.unsafe_set(0, 0)
                    constParts.ends->Js_array2.unsafe_set(0, maxI)
                    invokeNext()
                }
            }
        }
    } else {
        let begin = ref(if (idxToMatch == 0) {0} else {constParts.ends->Js_array2.unsafe_get(idxToMatch-1)+1})
        let maxBegin = exprLen - frmConstParts.remainingMinLength->Js_array2.unsafe_get(idxToMatch)
        parenCnt->parenCntReset
        let pState = ref(Balanced)
        let numOfVars = lengthOfGap2(idxToMatch-1,frmConstParts,frmExprLen)
        for _ in 1 to numOfVars {
            pState.contents = parenCnt->parenCntPut(expr->Js_array2.unsafe_get(begin.contents))
            begin.contents = begin.contents + 1
        }
        let partLen = frmConstParts.ends->Js_array2.unsafe_get(idxToMatch) - frmConstParts.begins->Js_array2.unsafe_get(idxToMatch) + 1
        let instr = ref(Continue)
        while (begin.contents <= maxBegin && pState.contents != Failed && instr.contents == Continue) {
            if (pState.contents == Balanced) {
                let matchedLen = ref(0)
                let cmpRes = ref(true)
                while (matchedLen.contents < partLen && cmpRes.contents) {
                    cmpRes.contents = frmExpr->Js_array2.unsafe_get(frmConstParts.begins->Js_array2.unsafe_get(idxToMatch)+matchedLen.contents) == expr->Js_array2.unsafe_get(begin.contents+matchedLen.contents)
                    matchedLen.contents = matchedLen.contents + 1
                }
                if (matchedLen.contents == partLen && cmpRes.contents) {
                    constParts.begins->Js_array2.unsafe_set(idxToMatch, begin.contents)
                    constParts.ends->Js_array2.unsafe_set(idxToMatch,begin.contents+partLen-1)
                    instr.contents = invokeNext()
                    parenCnt->parenCntReset
                }
            }
            pState.contents = parenCnt->parenCntPut(expr->Js_array2.unsafe_get(begin.contents))
            begin.contents = begin.contents + 1
        }
        instr.contents
    }
}

let createVarGroups = (~frmExpr:expr, ~frmConstParts:constParts): array<varGroup> => {
    let frmExprLen = frmExpr->Js_array2.length
    if (frmConstParts.length == 0) {
        [{
            leftConstPartIdx: -1,
            frmExpr:frmExpr,
            varsBeginIdx: 0,
            numOfVars: frmExprLen,
            exprBeginIdx: 0,
            exprEndIdx: 0
        }]
    } else {
        let res = []
        if (frmConstParts.begins->Js_array2.unsafe_get(0) != 0) {
            res->Js_array2.push({
                leftConstPartIdx: -1,
                frmExpr:frmExpr,
                varsBeginIdx:0,
                numOfVars:frmConstParts.begins->Js_array2.unsafe_get(0),
                exprBeginIdx: 0,
                exprEndIdx: 0
            })->ignore
        }
        for i in 0 to frmConstParts.length-2 {
            res->Js_array2.push({
                leftConstPartIdx: i,
                frmExpr:frmExpr,
                varsBeginIdx: frmConstParts.ends->Js_array2.unsafe_get(i)+1,
                numOfVars: lengthOfGap2(i, frmConstParts, frmExprLen),
                exprBeginIdx: 0,
                exprEndIdx: 0
            })->ignore
        }
        let lastConstPartIdx = frmConstParts.length-1
        if (frmConstParts.ends->Js_array2.unsafe_get(lastConstPartIdx) != frmExprLen-1) {
            res->Js_array2.push({
                leftConstPartIdx: lastConstPartIdx,
                frmExpr:frmExpr,
                varsBeginIdx: frmConstParts.ends->Js_array2.unsafe_get(lastConstPartIdx)+1,
                numOfVars: lengthOfGap2(lastConstPartIdx, frmConstParts, frmExprLen),
                exprBeginIdx: 0,
                exprEndIdx: 0
            })->ignore
        }
        res
    }
}

let initVarGroups = (~varGroups:array<varGroup>, ~constParts:constParts, ~expr:expr) => {
    let exprLen = expr->Js_array2.length
    if (constParts.length == 0) {
        (varGroups->Js_array2.unsafe_get(0)).exprBeginIdx = 0
        (varGroups->Js_array2.unsafe_get(0)).exprEndIdx = exprLen-1
    } else {
        varGroups->Js_array2.forEach(grp => {
            if (grp.leftConstPartIdx == -1) {
                grp.exprBeginIdx = 0
                grp.exprEndIdx = constParts.begins->Js_array2.unsafe_get(0) - 1
            } else if (grp.leftConstPartIdx == constParts.length-1) {
                grp.exprBeginIdx = constParts.ends->Js_array2.unsafe_get(grp.leftConstPartIdx)+1
                grp.exprEndIdx = exprLen-1
            } else {
                grp.exprBeginIdx = constParts.ends->Js_array2.unsafe_get(grp.leftConstPartIdx)+1
                grp.exprEndIdx = constParts.begins->Js_array2.unsafe_get(grp.leftConstPartIdx+1)-1
            }
        })
        varGroups->Js.Array2.sortInPlaceWith((g1,g2) => {
            if (g1.numOfVars < g2.numOfVars) {
                -1
            } else if (g1.numOfVars == g2.numOfVars) {
                0
            } else {
                1
            }
        })->ignore
    }
}

let rec iterateVarGroups = (
    ~expr:expr,
    ~subs:subs,
    ~varGroups:array<varGroup>,
    ~curGrpIdx:int,
    ~curVarIdx:int,
    ~subExprBeginIdx:int,
    ~parenCnt:parenCnt,
    ~consumer: subs=>contunieInstruction
): contunieInstruction => {
    let grp = varGroups->Js_array2.unsafe_get(curGrpIdx)
    let frmVar = grp.frmExpr->Js_array2.unsafe_get(grp.varsBeginIdx+curVarIdx)
    let maxSubExprLength = grp.exprEndIdx - subExprBeginIdx + 1 - (grp.numOfVars - curVarIdx - 1)
    
    let invokeNext = (subExprLength:int):contunieInstruction => {
        if (curVarIdx < grp.numOfVars - 1) {
            iterateVarGroups(
                ~expr,
                ~subs,
                ~varGroups,
                ~curGrpIdx,
                ~curVarIdx = curVarIdx+1,
                ~subExprBeginIdx = subExprBeginIdx+subExprLength,
                ~parenCnt,
                ~consumer
            )
        } else if (curGrpIdx < varGroups->Js_array2.length-1) {
            iterateVarGroups(
                ~expr,
                ~subs,
                ~varGroups,
                ~curGrpIdx = curGrpIdx+1,
                ~curVarIdx = 0,
                ~subExprBeginIdx = (varGroups->Js_array2.unsafe_get(curGrpIdx+1)).exprBeginIdx,
                ~parenCnt,
                ~consumer
            )
        } else {
            consumer(subs)
        }
    }

    let continueInstr = ref(Continue)
    if (!(subs.isDefined->Js_array2.unsafe_get(frmVar))) {
        subs.isDefined->Js_array2.unsafe_set(frmVar,true)
        subs.exprs->Js_array2.unsafe_set(frmVar,expr)
        subs.begins->Js_array2.unsafe_set(frmVar,subExprBeginIdx)
        if (curVarIdx == grp.numOfVars-1) {
            subs.ends->Js_array2.unsafe_set(frmVar,grp.exprEndIdx)
            continueInstr.contents = invokeNext(maxSubExprLength)
        } else {
            let subExprLength = ref(1)
            let end = ref(subExprBeginIdx)
            parenCnt->parenCntReset
            let pStatus = ref(Balanced)
            while (subExprLength.contents <= maxSubExprLength && continueInstr.contents == Continue && pStatus.contents != Failed) {
                subs.ends->Js_array2.unsafe_set(frmVar,end.contents)
                pStatus.contents = parenCnt->parenCntPut(expr->Js_array2.unsafe_get(end.contents))
                if (pStatus.contents == Balanced) {
                    continueInstr.contents = invokeNext(subExprLength.contents)
                    parenCnt->parenCntReset
                }
                subExprLength.contents = subExprLength.contents + 1
                end.contents = end.contents + 1
            }
        }
        subs.isDefined->Js_array2.unsafe_set(frmVar,false)
    } else {
        let existingExpr = subs.exprs->Js_array2.unsafe_get(frmVar)
        let existingExprBeginIdx = subs.begins->Js_array2.unsafe_get(frmVar)
        let existingExprLen = subs.ends->Js_array2.unsafe_get(frmVar) - existingExprBeginIdx + 1
        if (existingExprLen <= maxSubExprLength && (curVarIdx < grp.numOfVars-1 || existingExprLen == maxSubExprLength)) {
            let checkedLen = ref(0)
            while (checkedLen.contents < existingExprLen 
                    && existingExpr->Js_array2.unsafe_get(existingExprBeginIdx+checkedLen.contents) == expr->Js_array2.unsafe_get(subExprBeginIdx+checkedLen.contents)) {
                        checkedLen.contents = checkedLen.contents + 1
            }
            if (checkedLen.contents == existingExprLen) {
                continueInstr.contents = invokeNext(existingExprLen)
            }
        }
    }
    continueInstr.contents
}

let iterateSubstitutions = (
    ~frmExpr:expr, 
    ~expr:expr, 
    ~frmConstParts:constParts, 
    ~constParts:constParts, 
    ~varGroups:array<varGroup>,
    ~subs:subs,
    ~parenCnt:parenCnt,
    ~consumer: subs => contunieInstruction
):contunieInstruction => {
    if (subs.size == 0) {
        if (frmExpr == expr) {
            consumer(subs)
        } else {
            Continue
        }
    } else {
        let exprLen = expr->Js_array2.length
        let frmExprLen = frmExpr->Js_array2.length
        if (exprLen < frmExprLen) {
            Continue
        } else {
            iterateConstParts(
                ~frmExpr, 
                ~expr, 
                ~frmConstParts, 
                ~constParts, 
                ~idxToMatch=0,
                ~parenCnt,
                ~consumer = constParts => {
                    if (varGroups->Js.Array2.length > 0) {
                        initVarGroups(~varGroups, ~constParts, ~expr)
                        iterateVarGroups(
                            ~expr,
                            ~subs,
                            ~varGroups,
                            ~curGrpIdx = 0,
                            ~curVarIdx = 0,
                            ~subExprBeginIdx = (varGroups->Js_array2.unsafe_get(0)).exprBeginIdx,
                            ~parenCnt,
                            ~consumer
                        )
                    } else {
                        consumer(subs)
                    }
                }
            )
        }
    }
}

let createSubs = (~numOfVars:int) => {
    {
        size: numOfVars,
        begins: Belt_Array.make(numOfVars, 0),
        ends: Belt_Array.make(numOfVars, 0),
        exprs: Belt_Array.make(numOfVars, []),
        isDefined: Belt_Array.make(numOfVars, false),
    }
}

//let numberOfStates = (numOfVars, subExprLength) => {
    //let n = subExprLen - 1
    //let k = numOfVars - 1

    //let res = ref(1)
    //let rem = ref(2)
    //let minI = n-k+1
    //for i in minI to n {
        //res.contents = Js.Math.imul(res.contents, i)
    //}
//}

//let numberOfStates = varGroup => {
    //let subExprLen = varGroup.exprEndIdx-varGroup.exprBeginIdx+1
    //let n = subExprLen - 1
    //let k = 
//}

let prepareFrmSubsDataForFrame = (frame):frmSubsData => {
    let hypsE = frame.hyps->Js.Array2.filter(hyp => hyp.typ == E)

    let frmConstPartsArr:array<constParts> = []
    let constPartsArr:array<constParts> = []
    let varGroupsArr:array<array<varGroup>> = []

    hypsE->Js_array2.forEach(hyp => {
        let frmConstParts = createConstParts(hyp.expr)
        let constParts = createMatchingConstParts(frmConstParts)
        let varGroups = createVarGroups(~frmExpr=hyp.expr, ~frmConstParts)
        frmConstPartsArr->Js.Array2.push(frmConstParts)->ignore
        constPartsArr->Js.Array2.push(constParts)->ignore
        varGroupsArr->Js.Array2.push(varGroups)->ignore
    })

    let frmConstParts = createConstParts(frame.asrt)
    let constParts = createMatchingConstParts(frmConstParts)
    let varGroups = createVarGroups(~frmExpr=frame.asrt, ~frmConstParts)
    frmConstPartsArr->Js.Array2.push(frmConstParts)->ignore
    constPartsArr->Js.Array2.push(constParts)->ignore
    varGroupsArr->Js.Array2.push(varGroups)->ignore

    let subs = createSubs(~numOfVars=frame.numOfVars)
    {
        frame,
        hypsE,
        numOfHypsE: hypsE->Js.Array2.length,
        frmConstParts:frmConstPartsArr,
        constParts:constPartsArr,
        varGroups:varGroupsArr,
        subs,
    }
}

let prepareFrmSubsData = (
    ~ctx:mmContext, 
    ~asrtsToSkip:Belt_HashSetString.t=Belt_HashSetString.make(~hintSize=0),
    ()
):Belt_MapString.t<frmSubsData> => {
    let frms = []
    ctx->forEachFrame(frame => {
        if (!(asrtsToSkip->Belt_HashSetString.has(frame.label))) {
            frms->Js_array2.push(prepareFrmSubsDataForFrame(frame))->ignore
        }
        None
    })->ignore
    Belt_MapString.fromArray(frms->Js_array2.map(frm => (frm.frame.label, frm)))
}

let applySubs = (~frmExpr:expr, ~subs:subs, ~createWorkVar:int=>int): expr => {
    let resultSize = ref(0)
    frmExpr->Js_array2.forEach(s => {
        if (s < 0) {
            resultSize.contents = resultSize.contents + 1
        } else if (subs.isDefined->Js_array2.unsafe_get(s)) {
            resultSize.contents = resultSize.contents + (subs.ends->Js_array2.unsafe_get(s)-subs.begins->Js_array2.unsafe_get(s)+1)
        } else {
            resultSize.contents = resultSize.contents + 1
        }
    })
    let res = Expln_utils_common.createArray(resultSize.contents)
    let e = ref(0)
    let r = ref(0)
    while (r.contents < resultSize.contents) {
        let s = frmExpr->Js_array2.unsafe_get(e.contents)
        if (s < 0) {
            res->Js_array2.unsafe_set(r.contents,s)
            r.contents = r.contents + 1
        } else if (subs.isDefined->Js_array2.unsafe_get(s)) {
            let subExpr = subs.exprs->Js_array2.unsafe_get(s)
            let len = (subs.ends->Js_array2.unsafe_get(s)-subs.begins->Js_array2.unsafe_get(s)+1)
            Expln_utils_common.copySubArray(~src=subExpr, ~srcFromIdx=subs.begins->Js_array2.unsafe_get(s), ~dst=res, ~dstFromIdx=r.contents, ~len)
            r.contents = r.contents + len
        } else {
            res->Js_array2.unsafe_set(r.contents,createWorkVar(s))
            r.contents = r.contents + 1
        }
        e.contents = e.contents + 1
    }
    res
}

let verifyDisjoints = (
    ~frmDisj:Belt_MapInt.t<Belt_SetInt.t>, 
    ~subs:subs, 
    ~isDisjInCtx:(int,int)=>bool,
    ~debugLevel:int,
):option<unifErr> => {
    let res = ref(None)
    frmDisj->Belt_MapInt.forEach((n,ms) => {
        if (res.contents->Belt.Option.isNone) {
            ms->Belt_SetInt.forEach(m => {
                if (res.contents->Belt.Option.isNone) {
                    let nExpr = subs.exprs->Js_array2.unsafe_get(n)
                    let nExprBegin = subs.begins->Js_array2.unsafe_get(n)
                    let nExprEnd = subs.ends->Js_array2.unsafe_get(n)
                    let mExpr = subs.exprs->Js_array2.unsafe_get(m)
                    let mExprBegin = subs.begins->Js_array2.unsafe_get(m)
                    let mExprEnd = subs.ends->Js_array2.unsafe_get(m)
                    for nExprI in nExprBegin to nExprEnd {
                        if (res.contents->Belt.Option.isNone) {
                            let nExprSym = nExpr->Js_array2.unsafe_get(nExprI)
                            if (nExprSym >= 0) {
                                for mExprI in mExprBegin to mExprEnd {
                                    if (res.contents->Belt.Option.isNone) {
                                        let mExprSym = mExpr->Js_array2.unsafe_get(mExprI)
                                        if (mExprSym >= 0) {
                                            if (nExprSym == mExprSym) {
                                                if (debugLevel == 0) {
                                                    res.contents = Some(UnifErr)
                                                } else {
                                                    res.contents = Some(DisjCommonVar({
                                                        frmVar1:n, 
                                                        expr1:nExpr->Js_array2.slice(~start=nExprBegin, ~end_=nExprEnd+1),
                                                        frmVar2:m, 
                                                        expr2:mExpr->Js_array2.slice(~start=mExprBegin, ~end_=mExprEnd+1),
                                                        commonVar:nExprSym,
                                                    }))
                                                }
                                            } else if (!isDisjInCtx(nExprSym, mExprSym)) {
                                                if (debugLevel == 0) {
                                                    res.contents = Some(UnifErr)
                                                } else {
                                                    res.contents = Some(Disj({
                                                        frmVar1:n, 
                                                        expr1:nExpr->Js_array2.slice(~start=nExprBegin, ~end_=nExprEnd+1),
                                                        var1:nExprSym,
                                                        frmVar2:m, 
                                                        expr2:mExpr->Js_array2.slice(~start=mExprBegin, ~end_=mExprEnd+1),
                                                        var2:mExprSym,
                                                    }))
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            })
        }
    })
    res.contents
}

//------------------------- TEST ---------------------------

let test_iterateConstParts: (~ctx:mmContext, ~frmExpr:expr, ~expr:expr, ~parens:string) => (array<(int,int)>, array<array<(int,int)>>) = (~ctx,~frmExpr,~expr, ~parens) => {
    let constPartsToArr = (constParts:constParts) => {
        constParts.begins->Js_array2.mapi((b,i)=>(b,constParts.ends->Js_array2.unsafe_get(i)))
    }
    let parenCnt = parenCntMake(ctx->ctxStrToIntsExn(parens), ())
    let frmConstParts = createConstParts(frmExpr)
    let constParts = createMatchingConstParts(frmConstParts)
    let matchingConstParts = []
    iterateConstParts(
        ~frmExpr, 
        ~expr, 
        ~frmConstParts, 
        ~constParts, 
        ~idxToMatch=0,
        ~parenCnt,
        ~consumer = constParts => {
            matchingConstParts->Js_array2.push(
                constPartsToArr(constParts)
            )->ignore
            Continue
        }
    )->ignore
    (
        constPartsToArr(frmConstParts),
        matchingConstParts
    )
}

let test_iterateSubstitutions: (~ctx:mmContext, ~frmExpr:expr, ~expr:expr, ~parens:string) => array<array<expr>> = (~ctx, ~frmExpr, ~expr, ~parens) => {
    let parenCnt = parenCntMake(ctx->ctxStrToIntsExn(parens), ())
    let frmConstParts = createConstParts(frmExpr)
    let constParts = createMatchingConstParts(frmConstParts)
    let varGroups = createVarGroups(~frmExpr, ~frmConstParts)
    let numOfVars = frmExpr
        ->Js_array2.filter(i => i >= 0)
        ->Belt_SetInt.fromArray
        ->Belt_SetInt.size
    let subs = createSubs(~numOfVars)
    let result = []
    iterateSubstitutions(
        ~frmExpr, 
        ~expr, 
        ~frmConstParts, 
        ~constParts, 
        ~varGroups,
        ~subs,
        ~parenCnt,
        ~consumer = subs => {
            let res = []
            for i in 0 to numOfVars-1 {
                res->Js_array2.push(
                    subs.exprs->Js_array2.unsafe_get(i)->Js_array2.slice(~start=subs.begins->Js_array2.unsafe_get(i), ~end_=subs.ends->Js_array2.unsafe_get(i)+1)
                )->ignore
            }
            result->Js_array2.push(res)->ignore
            Continue
        }
    )->ignore
    result
}