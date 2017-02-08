// $begin{copyright}
//
// This file is part of WebSharper
//
// Copyright (c) 2008-2014 IntelliFactory
//
// Licensed under the Apache License, Version 2.0 (the "License"); you
// may not use this file except in compliance with the License.  You may
// obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
// implied.  See the License for the specific language governing
// permissions and limitations under the License.
//
// $end{copyright}

namespace WebSharper.JavaScript.Dom

open WebSharper.InterfaceGenerator
module P = Pattern

[<AutoOpen>]
module private Util =
    let GetNS = T<string>?namespaceURI * T<string>?localName
    let SetNS = T<string>?namespaceURI * T<string>?qualifiedName

[<AutoOpen>]
module private Types =
    let DOMTimeStamp = T<System.DateTime>
    let DocumentType = Class "DocumentType"
    let Document = Class "Document"
    let NodeList = Class "NodeList"
    let NamedNodeMap = Class "NamedNodeMap"
    let Element = Class "Element"
    let TypeInfo = Class "TypeInfo"
    let DOMLocator = Class "DOMLocator"
    let Event = Class "Event"
    let AbstractView = Class "AbstractView"

[<AutoOpen>]
module private Enumerations =

    let private Prepare (suffix: string) (x: string) =
        x.Substring(0, x.Length - suffix.Length).Split('_')
        |> Seq.filter ((<>) "")
        |> Seq.map (fun x ->
            x.Substring(0, 1) + x.Substring(1).ToLower())
        |> String.concat ""

    let private Enum name prefix suffix (names: string) =
        names.Split(' ')
        |> Seq.filter ((<>) "")
        |> Seq.map (fun x ->
            (Prepare suffix x, prefix + x))
        |> P.EnumInlines name

    let DOMExceptionType =
        Enum "DOMExceptionType" "DOMException." "_ERR" "\
            INDEX_SIZE_ERR DOMSTRING_SIZE_ERR HIERARCHY_REQUEST_ERR
            WRONG_DOCUMENT_ERR INVALID_CHARACTER_ERR NO_DATA_ALLOWED_ERR \
            NO_MODIFICATION_ALLOWED_ERR NOT_FOUND_ERR NOT_SUPPORTED_ERR \
            INUSE_ATTRIBUTE_ERR INVALID_STATE_ERR SYNTAX_ERR \
            INVALID_MODIFICATION_ERR NAMESPACE_ERR INVALID_ACCESS_ERR \
            VALIDATION_ERR TYPE_MISMATCH_ERR"

    let NodeType =
        Enum "NodeType" "Node." "_NODE" "\
            ELEMENT_NODE ATTRIBUTE_NODE TEXT_NODE CDATA_SECTION_NODE \
            ENTITY_REFERENCE_NODE ENTITY_NODE PROCESSING_INSTRUCTION_NODE \
            COMMENT_NODE DOCUMENT_NODE DOCUMENT_TYPE_NODE \
            DOCUMENT_FRAGMENT_NODE NOTATION_NODE"

    let DocumentPosition =
        Enum "DocumentPosition" "Node.DOCUMENT_POSITION_" "" "\
            DISCONNECTED PRECEDING FOLLOWING CONTAINS \
            CONTAINED_BY IMPLEMENTATION_SPECIFIC"

    let DerivationMethod =
        Enum "DerivationMethod" "TypeInfo.DERIVATION_" "" "\
            RESTRICTION EXTENSION UNION LIST"

    let NodeOperation =
        Enum "NodeOperation" "UserDataHandler.NODE_" "" "\
            IMPORTED DELETED RENAMED ADOPTED"

    let ErrorSeverity =
        Enum "ErrorSeverity" "DOMError.SEVERITY_" "" "\
            WARNING ERROR FATAL_ERROR"

    let PhaseType =
        Enum "PhaseType" "Event." "" "\
            AT_TARGET BUBBLING_PHASE CAPTURING_PHASE"

    let DeltaModeCode =
        Enum "DeltaModeCode" "WheelEvent." "" "\
            DOM_DELTA_PIXEL DOM_DELTA_LINE DOM_DELTA_PAGE"

    let InputModeCode =
        Enum "InputModeCode" "TextEvent.DOM_INPUT_METHOD_" "" "\
            UNKNOWN KEYBOARD PASTE DROP IME OPTION \
            HANDWRITING VOICE MULTIMODAL SCRIPT"

    let KeyLocationCode =
        Enum "KeyLocationCode" "KeyboardEvent.DOM_KEY_LOCATION_" "" "\
            LEFT NUMPAD RIGHT STANDARD MOBILE JOYSTICK"

    let attrChangeType =
        Enum "attrChangeType" "MutationEvent." "" "\
            ADDITION MODIFICATION REMOVAL"

module Interfaces =

    let DOMException =
        Class "DomException"
        |+> Static [
                "code" =@ DOMExceptionType
            ]

    let DOMStringList =
        Class "DomStringList"
        |+> Instance [
                "length" =@ T<int>
                "contains" => T<string->bool>
                "item" => T<int->string>
            ]

    let NameList =
        Class "NameList"
        |+> Instance [
                "length" =@ T<int>
                "getName" => T<int->string>
                "getNamespaceURI" => T<int->string>
                "contains" => T<string->bool>
                "containsNS" => T<string>?namespaceURI * T<string>?name ^-> T<bool>
            ]

    let DOMImplementation =
        Class "DOMImplementation"
        |+> Instance [
                "hasFeature" =>
                    T<string>?feature * T<string>?version ^-> T<bool>
                "createDocumentType" =>
                    T<string>?qualifiedName *
                    T<string>?publicId *
                    T<string>?systemId ^-> DocumentType
                "createDocument" =>
                    T<string>?namespaceURI *
                    T<string>?qualifiedName *
                    DocumentType ^-> Document
                "getFeature" => T<string>?feature * T<string>?version ^-> T<obj>
            ]

    let DOMImplementationList =
        Class "DomImplementationList"
        |+> Instance [
                "item" => T<int> ^-> DOMImplementation
                "length" =@ T<int>
            ]

    let DOMImpementationSource =
        Class "DomImplementationSource"
        |+> Instance [
                "getDOMImplementation" =>
                    T<string> ^-> DOMImplementation
                "getDOMImplementationList" =>
                    T<string> ^-> DOMImplementationList
            ]

    let DOMRect =
        Class "DomRect"
        |+> Instance [
                "x" =? T<double>
                "y" =? T<double>
                "width" =? T<double>
                "height" =? T<double>
                "top" =? T<double>
                "right" =? T<double>
                "bottom" =? T<double>
                "left" =? T<double>
            ]

    let EventTarget =
        let EventListener = (T<unit> + Event) ^-> T<unit>
        Class "EventTarget"
        |+> Static [
                Constructor T<unit>
            ]
        |+> Instance [
                "addEventListener" =>
                    T<string>?eventtype *
                    EventListener?listener *
                    T<bool>?useCapture ^-> T<unit>
                "addEventListenerNS" =>
                    T<string>?namespaceURI *
                    T<string>?eventtype *
                    EventListener?listener *
                    T<bool>?useCapture ^-> T<unit>
                "dispatchEvent" => Event ^-> T<bool>
                "removeEventListener" =>
                    T<string>?eventtype *
                    EventListener?listener *
                    T<bool>?useCapture ^-> T<unit>
                "removeEventListenerNS" =>
                    T<string>?namespaceURI *
                    T<string>?eventtype *
                    EventListener?listener *
                    T<bool>?useCapture ^-> T<unit>
            ]

    let QuerySelectorMixin =
        Instance [
            "querySelector" => T<string> ^-> Element
            "querySelectorAll" => T<string> ^-> NodeList
        ]

    let Node =
        Class "Node"
        |=> Inherits EventTarget
        |+> Instance [
                "attributes" =@ NamedNodeMap
                "baseURI" =@ T<string>
                "childNodes" =@ NodeList
                "firstChild" =? TSelf
                "lastChild" =@ TSelf
                "localName" =@ T<string>
                "namespaceURI" =@ T<string>
                "nextSibling" =@ TSelf
                "nodeName" =@ T<string>
                "nodeType" =@ NodeType
                "nodeValue" =@ T<string>
                "ownerDocument" =@ Document
                "parentNode" =@ TSelf
                "prefix" =@ T<string>
                "previousSibling" =@ TSelf
                "textContent" =@ T<string>
                "appendChild" => TSelf?newChild ^-> TSelf
                "cloneNode" => T<bool>?deep ^-> TSelf
                "compareDocumentPosition" => TSelf ^-> DocumentPosition
                "getFeature" => T<string>?feature * T<string>?version ^-> T<obj>
                "getUserData" => T<string>?key ^-> T<obj>
                "hasAttributes" => T<unit->bool>
                "hasChildNodes" => T<unit->bool>
                "insertBefore" => TSelf?newChild * TSelf?refChild ^-> TSelf
                "isDefaultNamespace" => T<string->bool>
                "isEqualNode" => TSelf ^-> T<bool>
                "isSameNode" => TSelf ^-> T<bool>
                "isSupported" =>
                    T<string>?feature * T<string>?version ^-> T<bool>
                "lookupNamespaceURI" => T<string->string>
                "lookupPrefix" => T<string->string>
                "normalize" => T<unit->unit>
                "removeChild" => TSelf?oldChild ^-> TSelf
                "replaceChild" => TSelf?newChild * TSelf?oldChild ^-> TSelf
                "setUserData" =>
                    T<string>?key *
                    T<obj>?data *
                    T<obj>?handler ^-> T<obj> |> Obsolete
            ]

    let NodeList =
        NodeList
        |+> Instance [
                "item" => T<int>?index ^-> Node
                |> WithInline "$this[$index]"
                "length" =@ T<int>
            ]

    let NamedNodeMap =
        NamedNodeMap
        |+> Instance [
                "getNamedItem" => T<string> ^-> Node
                "setNamedItem" => Node ^-> Node
                "removeNamedItem" => T<string> ^-> Node
                "item" => T<int> ^-> Node
                "length" =@ T<int>
                "getNamedItemNS" => GetNS ^-> Node
                "setNamedItemNS" => Node ^-> Node
                "removeNamedItemNS" => GetNS ^-> Node
            ]

    let CharacterData =
        Class "CharacterData"
        |=> Inherits Node
        |+> Instance [
                "data" =@ T<string>
                "length" =@ T<int>
                "substringData" =>
                    T<int>?offset * T<int>?count ^-> T<string>
                "appendData" => T<string->unit>
                "insertData" => T<int>?offset * T<string> ^-> T<unit>
                "deleteData" => T<int>?offset * T<int>?count ^-> T<unit>
                "replaceData" =>
                    T<int>?offset * T<int>?count * T<string> ^-> T<unit>
            ]

    let Attr =
        Class "Attr"
        |=> Inherits Node
        |+> Instance [
                "name" =@ T<string>
                "specified" =@ T<bool>
                "value" =@ T<string>
                "ownerElement" =@ Element
                "schemaTypeInfo" =@ TypeInfo
                "isId" =@ T<bool>
            ]

    let Element =
        Element
        |=> Inherits Node
        |+> QuerySelectorMixin
        |+> Instance [
                "schemaTypeInfo" =@ TypeInfo
                "tagName" =@ T<string>

                // CSSOM
                "scrollTop" =@ T<double>
                "scrollLeft" =@ T<double>
                "scrollWidth" =? T<double>
                "scrollHeight" =? T<double>
                "clientTop" =? T<double>
                "clientLeft" =? T<double>
                "clientWidth" =? T<double>
                "clientHeight" =? T<double>

                "getClientRects" => T<unit> ^-> Type.ArrayOf DOMRect
                "getBoundingClientRect" => T<unit> ^-> DOMRect
                // CSSOM

                "getAttribute" => T<string->string>
                "setAttribute" => T<string> * T<string> ^-> T<unit>
                "removeAttribute" => T<string->unit>
                "getAttributeNode" => T<string> ^-> Attr
                "setAttributeNode" => Attr ^-> Attr
                "removeAttributeNode" => Attr ^-> Attr
                "getElementsByTagName" => T<string> ^-> NodeList
                "getAttributeNS" => GetNS ^-> T<string>
                "setAttributeNS" => SetNS * T<string> ^-> T<unit>
                "removeAttributeNS" => GetNS ^-> T<unit>
                "getAttributeNodeNS" => GetNS ^-> Attr
                "setAttributeNodeNS" => Attr ^-> Attr
                "getElementsByTagNameNS" => GetNS ^-> NodeList
                "hasAttribute" => T<string->bool>
                "hasAttributeNS" => GetNS ^-> T<bool>
                "setIdAttribute" => T<string> * T<bool>?isId ^-> T<unit>
                "setIdAttributeNS" => GetNS * T<bool>?isId ^-> T<unit>
                "setIdAttributeNode" => Attr * T<bool>?isId ^-> T<unit>
            ]

    let Text =
        Class "Text"
        |=> Inherits CharacterData
        |+> Instance [
                "splitText" => T<int> ^-> TSelf
                "isElementContentWhiteSpace" =@ T<bool>
                "wholeText" =@ T<string>
                "replaceWholeText" => T<string> ^-> TSelf
            ]

    let Comment =
        Class "Comment"
        |=> Inherits CharacterData

    let TypeInfo =
        TypeInfo
        |+> Instance [
                "typeName" =@ T<string>
                "typeNamespace" =@ T<string>
                "isDerivedFrom" =>
                    T<string>?typeNamespace *
                    T<string>?typeName *
                    DerivationMethod?derivationMethod ^-> T<bool>
            ]

    let UserDataHandler =
        Class "UserDataHandler"
        |+> Instance [
                "handle" =>
                    NodeOperation * T<string>?key * T<obj>?data *
                    Node?src * Node?dst ^-> T<unit>
            ]

    let DOMError =
        Class "DOMError"
        |+> Instance [
                "severity" =@ ErrorSeverity
                "message" =@ T<string>
                "type" =@ T<string>
                "relatedException" =@ T<obj>
                "relatedData" =@ T<obj>
                "location" =@ DOMLocator
            ]

    let DOMErrorHandler =
        Class "DOMErrorHandler"
        |+> Instance [
                "handleError" => DOMError ^-> T<bool>
            ]

    let DOMLocator =
        DOMLocator
        |+> Instance [
                "lineNumber" =@ T<int>
                "columnNumber" =@ T<int>
                "byteOffset" =@ T<int>
                "utf16Offset" =@ T<int>
                "relatedNode" =@ Node
                "uri" =@ T<string>
            ]

    let DOMConfiguration =
        Class "DOMConfiguration"
        |+> Instance [
                "setParameter" => T<string*obj->unit>
                "getParameter" => T<string->obj>
                "canSetParameter" => T<string*obj->bool>
                "parameterNames" =@ DOMStringList
            ]

    let CDATASection =
        Class "CDATASection"
        |=> Inherits Text

    let DocumentType =
        DocumentType
        |+> Instance [
                "name" =@ T<string>
                "entities" =@ NamedNodeMap
                "notations" =@ NamedNodeMap
                "publicId" =@ T<string>
                "systemId" =@ T<string>
                "internalSubset" =@ T<string>
            ]

    let Notation =
        Class "Notation"
        |=> Inherits Node
        |+> Instance [
                "publicId" =@ T<string>
                "systemId" =@ T<string>
            ]

    let Entity =
        Class "Entity"
        |=> Inherits Node
        |+> Instance [
                "publicId" =@ T<string>
                "systemId" =@ T<string>
                "notationName" =@ T<string>
                "inputEncoding" =@ T<string>
                "xmlEncoding" =@ T<string>
                "xmlVersion" =@ T<string>
            ]

    let EntityReference =
        Class "EntityReference"
        |=> Inherits Node

    let ProcessingInstruction =
        Class "ProcessingInstruction"
        |=> Inherits Node
        |+> Instance [
                "target" =@ T<string>
                "data" =@ T<string>
            ]

    let DocumentFragment =
        Class "DocumentFragment"
        |=> Inherits Node

    let CustomEvent  =
        Class "CustomEvent"
        |+> Instance [
                "detail" =@ T<obj>
                "initCustomEvent" =>
                    T<string>?typeArg *
                    T<bool>?canBubbleArg *
                    T<bool>?cancelableArg *
                    T<obj>?detailArg ^-> T<unit>
                "initCustomEventNS" =>
                    T<string>?namespaceURIArg *
                    T<string>?typeArg *
                    T<bool>?canBubbleArg *
                    T<bool>?cancelableArg *
                    T<obj>?detailArg ^-> T<unit>
            ]

    let EventInit =
        Pattern.Config "EventInit" {
            Required = []
            Optional =
                [
                    "bubbles", T<bool>
                    "cancelable", T<bool>
                    "scoped", T<bool>
                    "composed", T<bool>
                ]
        }

    let Event =
        Event
        |+> Static [
                Constructor (T<string> * !? EventInit)
            ]
        |+> Instance [
                "bubbles" =@ T<bool>
                "cancelable" =@ T<bool>
                "currentTarget" =@ EventTarget
                "defaultPrevented" =@ T<bool>
                "eventPhase" =@ PhaseType
                "namespaceURI" =@ T<string>
                "target" =@ EventTarget
                "timeStamp" =@ DOMTimeStamp
                "time" =@ T<string>
                "initEvent" =>
                    T<string>?eventTypeArg *
                    T<bool>?canBubbleArg *
                    T<bool>?cancelableArg ^-> T<unit>
                "initEventNS" =>
                    T<string>?namespaceURIArg *
                    T<string>?eventTypeArg *
                    T<bool>?canBubbleArg *
                    T<bool>?cancelableArg ^-> T<unit>
                "preventDefault" => T<unit->unit>
                "stopImmediatePropagation" => T<unit->unit>
                "stopPropagation" => T<unit->unit>
            ]

    let DocumentView =
        Class "DocumentView"
        |+> Instance [
                "defaultView" => AbstractView
            ]

    let AbstractView =
        AbstractView
        |+> Instance [
                "document" =@ DocumentView
            ]

    let UIEvent =
        Class "UIEvent"
        |=> Inherits Event
        |+> Instance [
                "detail" =@ T<int>
                "view" =@ AbstractView
                "initUIEvent" =>
                    T<string>?typeArg *
                    T<bool>?canBubbleArg *
                    T<bool>?cancelableArg *
                    AbstractView?viewArg *
                    T<int>?detailArg ^-> T<unit>
                "initUIEventNS" =>
                    T<string>?namespaceURIArg *
                    T<string>?typeArg *
                    T<bool>?canBubbleArg *
                    T<bool>?cancelableArg *
                    AbstractView?viewArg *
                    T<int>?detailArg ^-> T<unit>
            ]

    let FocusEvent =
        Class "FocusEvent"
        |=> Inherits UIEvent
        |+> Instance [
            "relatedTarget" =@ EventTarget
        ]

    let MouseEvent =
        Class "MouseEvent"
        |=> Inherits UIEvent
        |+> Instance [
                "altKey" =@ T<bool>
                "button" =@ T<int> // short
                "clientX" =@ T<int>
                "clientY" =@ T<int>
                "ctrlKey" =@ T<bool>
                "metaKey" =@ T<bool>
                "relatedTarget" =@ EventTarget
                "screenX" =@ T<int>
                "screenY" =@ T<int>
                "shiftKey" =@ T<bool>
                "getModifierState" => T<string>?keyIdentifierArg ^-> T<bool>
                "initMouseEvent" =>
                    T<string>?typeArg *
                    T<bool>?canBubbleArg *
                    T<bool>?cancelableArg *
                    AbstractView?viewArg *
                    T<int>?detailArg *
                    T<int>?screenXArg *
                    T<int>?screenYArg *
                    T<int>?clientXArg *
                    T<int>?clientYArg *
                    T<bool>?ctrlKeyArg *
                    T<bool>?altKeyArg *
                    T<bool>?shiftKeyArg *
                    T<bool>?metaKeyArg *
                    T<int>?button *
                    Node?relatedTargetArg ^-> T<unit>
                "initMouseEventNS" =>
                    T<string>?namespaceURIArg *
                    T<string>?typeArg *
                    T<bool>?canBubbleArg *
                    T<bool>?cancelableArg *
                    AbstractView?viewArg *
                    T<int>?detailArg *
                    T<int>?screenXArg *
                    T<int>?screenYArg *
                    T<int>?clientXArg *
                    T<int>?clientYArg *
                    T<int>?button *
                    Node?relatedTargetArg *
                    T<string>?modifiersListArg ^-> T<unit>
            ]

    let MouseWheelEvent =
        Class "MouseWheelEvent"
        |=> Inherits MouseEvent
        |+> Instance [
                "wheelDelta" =@ T<int>
                "initMouseWheelEvent" =>
                    T<string>?typeArg *
                    T<bool>?canBubbleArg *
                    T<bool>?cancelableArg *
                    AbstractView?viewArg *
                    T<int>?detailArg *
                    T<int>?screenXArg *
                    T<int>?screenYArg *
                    T<int>?clientXArg *
                    T<int>?clientYArg *
                    T<int>?button *
                    Node?relatedTargetArg *
                    T<string>?modifiersListArg *
                    T<int>?wheelDeltaArg ^-> T<unit>
                "initMouseWheelEventNS" =>
                    T<string>?namespaceURIArg *
                    T<string>?typeArg *
                    T<bool>?canBubbleArg *
                    T<bool>?cancelableArg *
                    AbstractView?viewArg *
                    T<int>?detailArg *
                    T<int>?screenXArg *
                    T<int>?screenYArg *
                    T<int>?clientXArg *
                    T<int>?clientYArg *
                    T<int>?button *
                    Node?relatedTargetArg *
                    T<string>?modifiersListArg *
                    T<int>?wheelDeltaArg ^-> T<unit>
            ]

    let WheelEvent =
        Class "WheelEvent"
        |=> Inherits MouseEvent
        |+> Instance [
                "deltaX" =@ T<int>
                "deltaY" =@ T<int>
                "deltaZ" =@ T<int>
                "deltaMode" =@ DeltaModeCode
                "initWheelEvent" =>
                    T<string>?typeArg *
                    T<bool>?canBubbleArg *
                    T<bool>?cancelableArg *
                    AbstractView?viewArg *
                    T<int>?detailArg *
                    T<int>?screenXArg *
                    T<int>?screenYArg *
                    T<int>?clientXArg *
                    T<int>?clientYArg *
                    T<int>?button *
                    Node?relatedTargetArg *
                    T<string>?modifiersListArg *
                    T<int>?wheelDeltaArg *
                    T<int>?deltaX *
                    T<int>?deltaY *
                    T<int>?deltaZ *
                    DeltaModeCode ^-> T<unit>
                "initWheelEventNS" =>
                    T<string>?namespaceURIArg *
                    T<string>?typeArg *
                    T<bool>?canBubbleArg *
                    T<bool>?cancelableArg *
                    AbstractView?viewArg *
                    T<int>?detailArg *
                    T<int>?screenXArg *
                    T<int>?screenYArg *
                    T<int>?clientXArg *
                    T<int>?clientYArg *
                    T<int>?button *
                    Node?relatedTargetArg *
                    T<string>?modifiersListArg *
                    T<int>?wheelDeltaArg *
                    T<int>?deltaX *
                    T<int>?deltaY *
                    T<int>?deltaZ *
                    DeltaModeCode ^-> T<unit>
            ]

    let TextEvent =
        Class "TextEvent"
        |=> Inherits Event
        |+> Instance [
                "data" =@ T<string>
                "inputMode" =@ InputModeCode
                "initTextEvent" =>
                    T<string>?typeArg *
                    T<bool>?canBubbleArg *
                    T<bool>?cancelableArg *
                    AbstractView *
                    T<string>?dataArg *
                    InputModeCode ^-> T<unit>
                "initTextEventNS" =>
                    T<string>?namespaceURIArg *
                    T<string>?typeArg *
                    T<bool>?canBubbleArg *
                    T<bool>?cancelableArg *
                    AbstractView *
                    T<string>?dataArg *
                    InputModeCode ^-> T<unit>
            ]

    let KeyboardEvent =
        Class "KeyboardEvent"
        |=> Inherits UIEvent
        |+> Instance [
                "altKey" =@ T<bool>
                "ctrlKey" =@ T<bool>
                "keyIdentifier" =@ T<string>
                "keyLocation" =@ KeyLocationCode
                "metaKey" =@ T<bool>
                "shiftKey" =@ T<bool>
                "repeat" =@ T<bool>
                "getModifierState" => T<string>?keyIdentifierArg ^-> T<bool>
                "initKeyboardEvent" =>
                    T<string>?typeArg *
                    T<bool>?canBubbleArg *
                    T<bool>?cancelableArg *
                    AbstractView *
                    T<string>?keyIdentifierArg *
                    KeyLocationCode *
                    T<string>?modifiersListArg ^-> T<unit>
                "initKeyboardEventNS" =>
                    T<string>?namespaceURIArg *
                    T<string>?typeArg *
                    T<bool>?canBubbleArg *
                    T<bool>?cancelableArg *
                    AbstractView *
                    T<string>?keyIdentifierArg *
                    KeyLocationCode *
                    T<string>?modifiersListArg ^-> T<unit>
            ]
    let CompositionEvent =
        Class "CompositionEvent"
        |=> Inherits UIEvent
        |+> Instance [
                "data" =@ T<string>
                "initCompositionEvent" =>
                    T<string>?typeArg *
                    T<bool>?canBubbleArg *
                    T<bool>?cancelableArg *
                    AbstractView *
                    T<string>?dataArg ^-> T<unit>
                "initCompositionEventNS" =>
                    T<string>?namespaceURIArg *
                    T<string>?typeArg *
                    T<bool>?canBubbleArg *
                    T<bool>?cancelableArg *
                    AbstractView *
                    T<string>?dataArg ^-> T<unit>
            ]

    let MutationEvent =
        Class "MutationEvent"
        |=> Inherits Event
        |+> Instance [
                "attrChange" =@ attrChangeType
                "attrName" =@ T<string>
                "newValue" =@ T<string>
                "prevValue" =@ T<string>
                "relatedNode" =@ Node
                "initMutationEvent" =>
                    T<string>?typeArg *
                    T<bool>?canBubbleArg *
                    T<bool>?cancelableArg *
                    Node?relatedNodeArg *
                    T<string>?prevValueArg *
                    T<string>?newValueArg *
                    T<string>?attrNameArg *
                    attrChangeType ^-> T<unit>
                "initMutationEventNS" =>
                    T<string>?namespaceURIArg *
                    T<string>?typeArg *
                    T<bool>?canBubbleArg *
                    T<bool>?cancelableArg *
                    Node?relatedNodeArg *
                    T<string>?prevValueArg *
                    T<string>?newValueArg *
                    T<string>?attrNameArg *
                    attrChangeType ^-> T<unit>
            ]

    let MutationNameEvent =
        Class "MutationNameEvent"
        |=> Inherits Event
        |+> Instance [
                "prevNamespaceURI" =@ T<string>
                "prevNodeName" =@ T<string>
                "initMutationNameEvent" =>
                    T<string>?typeArg *
                    T<bool>?canBubbleArg *
                    T<bool>?cancelableArg *
                    Node?relatedNodeArg *
                    T<string>?prevNamespaceURIArg *
                    T<string>?prevNodeNameArg ^-> T<unit>
                "initMutationNameEventNS" =>
                    T<string>?namespaceURIArg *
                    T<string>?typeArg *
                    T<bool>?canBubbleArg *
                    T<bool>?cancelableArg *
                    Node?relatedNodeArg *
                    T<string>?prevNamespaceURIArg *
                    T<string>?prevNodeNameArg ^-> T<unit>
            ]

    let DocumentEvent =
        Class "DocumentEvent"
        |+> Instance [
                "canDispatch" => T<string>?namespaceURI * T<string>?eventtype ^-> T<bool>
                "createEvent" => T<string>?eventType ^-> Event // user needs to downcast to the right event
                // the following methods are non-standard
                "createCustomEvent" => T<unit> ^-> CustomEvent
                |> WithInline "$0.createEvent(\"CustomEvent\")"
                "createMouseEvent" => T<unit> ^-> MouseEvent
                |> WithInline "$0.createEvent(\"MouseEvent\")"
                "createMouseWheelEvent" => T<unit> ^-> MouseWheelEvent
                |> WithInline "$0.createEvent(\"MouseWheelEvent\")"
                "createTextEvent" => T<unit> ^-> TextEvent
                |> WithInline "$0.createEvent(\"TextEvent\")"
                "createKeyboardEvent" => T<unit> ^-> KeyboardEvent
                |> WithInline "$0.createEvent(\"TextEvent\")"
                "createCompositionEvent" => T<unit> ^-> CompositionEvent
                |> WithInline "$0.createEvent(\"CompositionEvent\")"
                "createMutationEvent" => T<unit> ^-> MutationEvent
                |> WithInline "$0.createEvent(\"MutationEvent\")"
                "createMutationNameEvent" => T<unit> ^-> MutationNameEvent
                |> WithInline "$0.createEvent(\"MutationNameEvent\")"
            ]

    let Document =
        Document
        |=> Inherits Node
        |+> QuerySelectorMixin
        |+> Instance [
                "cookie" =@ T<string>
                "body" =@ Element
                "doctype" =@ DocumentType
                "documentElement" =@ Element
                "documentURI" =@ T<string>
                "domConfig" =@ DOMConfiguration
                "inputEncoding" =@ T<string>
                "implementation" =@ DOMImplementation
                "strictErrorChecking" =@ T<bool>
                "xmlEncoding" =@ T<string>
                "xmlStandalone" =@ T<bool>
                "xmlVersion" =@ T<string>
                "adoptNode" => Node ^-> Node
                "createAttribute" => T<string> ^-> Attr
                "createAttributeNS" =>
                    T<string>?namespaceURI *
                    T<string>?qualifiedName ^-> Attr
                "createCDATASection" => T<string> ^-> CDATASection
                "createComment" => T<string> ^-> Comment
                "createDocumentFragment" => T<unit> ^-> DocumentFragment
                "createElement" => T<string> ^-> Element
                "createElementNS" =>
                    T<string>?namespaceURI *
                    T<string>?qualifiedName ^-> Element
                "createEntityReference" => T<string> ^-> EntityReference
                "createProcessingInstruction" =>
                    T<string>?target *
                    T<string>?data ^-> ProcessingInstruction
                "createTextNode" => T<string> ^-> Text
                "getElementById" => T<string>?id ^-> Element
                "getElementsByTagName" => T<string> ^-> NodeList
                "getElementsByTagNameNS" =>
                    T<string>?namespaceURI *
                    T<string>?localName ^-> NodeList
                "importNode" => Node?importedNode * T<bool>?deep ^-> Node
                "normalizeDocument" => T<unit->unit>
                "renameNode" =>
                    Node *
                    T<string>?namespaceURI *
                    T<string>?qualifiedName ^-> Node
            ]
        |+> Static [
                "Current" =? Document
                |> WithGetterInline "document"
                |> ObsoleteWithMessage "Use JS.Document or JS.Window.Document instead."
            ]

module Definition =
    module E = Enumerations
    module I = Interfaces

    let Namespaces =
        [
            Namespace "WebSharper.JavaScript.Dom" [
                I.Attr
                I.CDATASection
                I.CharacterData
                I.Comment
                I.DOMConfiguration
                I.DOMError
                I.DOMErrorHandler
                I.DOMException
                I.DOMImpementationSource
                I.DOMImplementation
                I.DOMImplementationList
                I.DOMLocator
                I.DOMStringList
                I.DOMRect
                I.Document
                I.DocumentFragment
                I.DocumentType
                I.Element
                I.Entity
                I.EntityReference
                I.NameList
                I.NamedNodeMap
                I.Node
                I.NodeList
                I.Notation
                I.ProcessingInstruction
                I.Text
                I.TypeInfo
                I.UserDataHandler
                I.Event
                I.EventInit
                I.EventTarget
                I.CustomEvent
                I.FocusEvent
                I.DocumentEvent
                I.DocumentView
                I.AbstractView
                I.UIEvent
                I.MouseEvent
                I.MouseWheelEvent
                I.WheelEvent
                I.TextEvent
                I.KeyboardEvent
                I.CompositionEvent
                I.MutationEvent
                I.MutationNameEvent
                E.DOMExceptionType
                E.DerivationMethod
                E.DocumentPosition
                E.ErrorSeverity
                E.NodeOperation
                E.NodeType
                E.PhaseType
                E.DeltaModeCode
                E.InputModeCode
                E.KeyLocationCode
                E.attrChangeType
            ]
        ]
