open Expln_test
open MM_parser
open MM_wrk_editor
open MM_statements_dto

let setMmPath = "./src/metamath/test/resources/set-no-proofs.mm"
let failOnMismatch = true
let debug = false

let curTestDataDir = ref("")

let setTestDataDir = dirName => {
    curTestDataDir.contents = "./src/metamath/test/resources/int-test-data/" ++ dirName
}

let proofStatusToStr = status => {
    switch status {
        | Ready => "ready"
        | Waiting => "waiting"
        | NoJstf => "noJstf"
        | JstfIsIncorrect => "jstfIsIncorrect"
    }
}

let editorStateToStr = st => {
    let lines = []
    lines->Js_array2.push("Variables:")->ignore
    lines->Js_array2.push(st.varsText)->ignore
    lines->Js_array2.push("")->ignore
    lines->Js_array2.push("Disjoints:")->ignore
    lines->Js_array2.push(st.disjText)->ignore
    lines->Js_array2.push("")->ignore
    st.stmts->Js.Array2.forEach(stmt => {
        lines->Js_array2.push("")->ignore
        lines->Js_array2.push(
            "--- "
            ++ (stmt.typ->userStmtTypeToStr)
            ++ " -------------------------------------------------------------------------------"
        )->ignore
        lines->Js_array2.push(stmt.label)->ignore
        lines->Js_array2.push(stmt.jstfText)->ignore
        lines->Js_array2.push(contToStr(stmt.cont))->ignore
        lines->Js_array2.push(
            stmt.proofStatus
                ->Belt_Option.map(status => (status->proofStatusToStr))
                ->Belt_Option.getWithDefault("None")
        )->ignore
        switch stmt.stmtErr {
            | None => ()
            | Some(msg) => lines->Js_array2.push("Error: " ++ msg)->ignore
        }
    })
    lines->Js.Array2.joinWith("\n")
}

let newStmtsDtoToStr = (newStmtsDto:stmtsDto):string => {
    let disjStr = newStmtsDto.newDisjStr->Js.Array2.sortInPlace->Js.Array2.joinWith("\n")
    let stmtsStr = newStmtsDto.stmts
        ->Js.Array2.map(stmt => {
            [
                stmt.label,
                switch stmt.jstf {
                    | None => ""
                    | Some({args, label}) => "[" ++ args->Js_array2.joinWith(" ") ++ " : " ++ label ++ " ]"
                },
                if (stmt.isProved) {"\u2713"} else {" "},
                stmt.exprStr
            ]->Js.Array2.joinWith(" ")
        })->Js.Array2.joinWith("\n")
    disjStr ++ "\n" ++ stmtsStr
}

let assertStrEqFile = (actualStr:string, expectedStrFileName:string) => {
    let fileWithExpectedResult = curTestDataDir.contents ++ "/" ++ expectedStrFileName ++ ".txt"
    let expectedResultStr = try {
        Expln_utils_files.readStringFromFile(fileWithExpectedResult)->Js.String2.replaceByRe(%re("/\r/g"), "")
    } catch {
        | Js.Exn.Error(exn) => {
            if (
                exn->Js.Exn.message
                    ->Belt_Option.getWithDefault("")
                    ->Js_string2.includes("no such file or directory")
            ) {
                ""
            } else {
                raise(MmException({msg:`Could not read from ${fileWithExpectedResult}`}))
            }
        }
    }
    if (actualStr != expectedResultStr) {
        let fileWithActualResult = fileWithExpectedResult ++ ".actual"
        Expln_utils_files.writeStringToFile(fileWithActualResult, actualStr)
        if (failOnMismatch) {
            assertEq( fileWithActualResult, fileWithExpectedResult )
        }
    }
}

let assertEditorState = (st, expectedStrFileName:string) => {
    let actualStr = st->editorStateToStr
    assertStrEqFile(actualStr, expectedStrFileName)
}

let assertProof = (st, stmtId:string, expectedStrFileName:string) => {
    let actualStr = st->generateCompressedProof(stmtId)
        ->Belt.Option.getWithDefault("no proof generated")
        ->Js.String2.replaceByRe(%re("/\r/g"), "")
    assertStrEqFile(actualStr, expectedStrFileName)
}

let assertTextsEq = (text1:string, fileName1:string, text2:string, fileName2:string):unit => {
    if (text1 != text2) {
        Expln_utils_files.writeStringToFile(
            curTestDataDir.contents ++ "/" ++ fileName1 ++ ".txt", 
            text1
        )
        Expln_utils_files.writeStringToFile(
            curTestDataDir.contents ++ "/" ++ fileName2 ++ ".txt", 
            text2
        )
        assertEq( text1, text2 )
    }
}

let assertTextEqFile = (actualStr:string, expectedStrFileName:string):unit => {
    assertStrEqFile(actualStr, expectedStrFileName)
}

let generateReducedMmFile = (
    ~pathToFullMmFile:string,
    ~pathToSaveTo:string,
    ~skipComments:bool=false,
    ~skipProofs:bool=false,
    ()
) => {
    let fullMmFileText = Expln_utils_files.readStringFromFile(pathToFullMmFile)
    let (ast, _) = parseMmFile(~mmFileContent=fullMmFileText, ~skipComments=true, ~skipProofs=true, ())
    let reducedContent = astToStr(ast)
    Expln_utils_files.writeStringToFile( pathToSaveTo, reducedContent )
}