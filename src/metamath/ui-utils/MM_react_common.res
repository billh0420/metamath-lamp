open Expln_React_Mui
open Expln_React_Modal
open Expln_utils_promise

@val external navigator: {..} = "navigator"
@val external window: {..} = "window"

let getAvailWidth = ():int => {
    window["screen"]["availWidth"]
}

let copyToClipboard = (text:string) => {
    navigator["clipboard"]["writeText"](. text)
}

let rndProgress = (~text:string, ~pct:option<float>=?, ~onTerminate:option<unit=>unit>=?, ()) => {
    <Paper style=ReactDOM.Style.make(~padding=onTerminate->Belt.Option.map(_=>"5px")->Belt.Option.getWithDefault("10px"), ())>
        <Row alignItems=#center spacing=1.>
            <span style=ReactDOM.Style.make(~paddingLeft="10px", ())>
                {
                    switch pct {
                        | Some(pct) => `${text}: ${(pct *. 100.)->Js.Math.round->Belt.Float.toInt->Belt_Int.toString}%`
                        | None => text
                    }->React.string
                }
            </span>
            {
                switch onTerminate {
                    | None => React.null
                    | Some(onTerminate) => {
                        <IconButton onClick={_ => onTerminate()}>
                            <MM_Icons.CancelOutlined/>
                        </IconButton>
                    }
                }
            }
        </Row>
    </Paper>
}

let rndInfoDialog = (~text:string, ~onOk:unit=>unit, ~title:option<string>=?, ()) => {
    <Paper style=ReactDOM.Style.make(~padding="10px", ())>
        <Col spacing=1.>
            <span 
                style=ReactDOM.Style.make(
                    ~fontWeight="bold", 
                    ~display=?{if (title->Belt_Option.isNone) {Some("none")} else {None}}, 
                    ()
                )
            >
                {title->Belt_Option.getWithDefault("")->React.string}
            </span>
            <span>
                {text->React.string}
            </span>
            <Button onClick={_=>onOk()} variant=#contained >
                {React.string("Ok")}
            </Button>
        </Col>
    </Paper>
}

let openInfoDialog = (~modalRef:modalRef, ~text:string, ~onOk:option<unit=>unit>=?, ~title:option<string>=?, ()) => {
    openModal(modalRef, _ => React.null)->promiseMap(modalId => {
        updateModal(modalRef, modalId, () => {
            rndInfoDialog(
                ~text, 
                ~onOk = () => {
                    closeModal(modalRef, modalId)
                    onOk->Belt_Option.forEach(clbk => clbk())
                },
                ~title?,
                ()
            )
        })
    })->ignore
}

let kbrdHnd = (
    ~onCtrlEnter: option<() => unit>=?,
    ~onEnter: option<() => unit>=?,
    ~onEsc: option<() => unit>=?,
    ()
):(ReactEvent.Keyboard.t => unit) => {
    (kbrdEvt:ReactEvent.Keyboard.t) => {
        let isAlt = kbrdEvt->ReactEvent.Keyboard.altKey
        let isCtrl = kbrdEvt->ReactEvent.Keyboard.ctrlKey
        let isShift = kbrdEvt->ReactEvent.Keyboard.shiftKey
        let keyCode = kbrdEvt->ReactEvent.Keyboard.keyCode

        onCtrlEnter->Belt.Option.forEach(onCtrlEnter => {
            if (!isAlt && isCtrl && !isShift && keyCode == 13) {
                onCtrlEnter()
            }
        })
        
        onEnter->Belt.Option.forEach(onEnter => {
            if (!isAlt && !isCtrl && !isShift && keyCode == 13) {
                onEnter()
            }
        })
        
        onEsc->Belt.Option.forEach(onEsc => {
            if (!isAlt && !isCtrl && !isShift && keyCode == 27) {
                onEsc()
            }
        })
    }
}

type mouseButton = Left | Middle | Right

type clickCallback = {
    btn:mouseButton,
    alt:bool,
    shift:bool,
    ctrl:bool,
    act:unit=>unit,
}

let mouseButtonToInt = (btn:mouseButton):int => {
    switch btn {
        | Left => 0
        | Middle => 1
        | Right => 2
    }
}

let clickClbkMake = (
    ~btn:mouseButton=Left,
    ~alt:bool=false,
    ~shift:bool=false,
    ~ctrl:bool=false,
    ~act:unit=>unit,
    ()
) => {
    { btn, alt, shift, ctrl, act, }
}

let clickHnd = (
    ~btn:mouseButton=Left,
    ~alt:bool=false,
    ~shift:bool=false,
    ~ctrl:bool=false,
    ~act:unit=>unit,
    ()
):(ReactEvent.Mouse.t => unit) => {
    evt => {
        if (
            evt->ReactEvent.Mouse.button === btn->mouseButtonToInt
            && evt->ReactEvent.Mouse.altKey === alt
            && evt->ReactEvent.Mouse.ctrlKey === ctrl
            && evt->ReactEvent.Mouse.shiftKey === shift
        ) {
            act()
        }
    }
}

let runCallback = (evt:ReactEvent.Mouse.t, clbk:clickCallback):unit => {
    if (
        evt->ReactEvent.Mouse.button === clbk.btn->mouseButtonToInt
        && evt->ReactEvent.Mouse.altKey === clbk.alt
        && evt->ReactEvent.Mouse.ctrlKey === clbk.ctrl
        && evt->ReactEvent.Mouse.shiftKey === clbk.shift
    ) {
        clbk.act()
    }
}

let clickHnd2 = ( clbk1:clickCallback, clbk2:clickCallback, ):(ReactEvent.Mouse.t => unit) => {
    evt => {
        runCallback(evt,clbk1)
        runCallback(evt,clbk2)
    }
}