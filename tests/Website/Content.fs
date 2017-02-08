// $begin{copyright}
//
// This file is part of WebSharper
//
// Copyright (c) 2008-2016 IntelliFactory
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

/// Declares server-side content utilities.
module Website.Content

open WebSharper
open WebSharper.Sitelets
open WebSharper.Sitelets.Tests.Server
module SampleSite = WebSharper.Sitelets.Tests.SampleSite

[<NoComparison>]
type FullAction =
    | Site of Actions.Action
    | SiteletsTests of SampleSite.Action
    | CSharpSiteletsTests of obj

let HomePage (ctx: Context<_>) =
    Content.Page(
        Title = "WebSharper tests",
        Body = [
            Elt("h1", Text "WebSharper tests")
            Elt("ul",
                Elt("li",
                    Elt("a",
                        Attr("href", ctx.Link (Site Actions.Tests)),
                        Text "Client-side test suite"
                    )
                ),
                Elt("li",
                    Elt("a",
                        Attr("href", ctx.Link (SiteletsTests SampleSite.Home)),
                        Text "Sitelets test minisite"
                    )
                ),
                Elt("li",
                    Elt("a",
                        Attr("href", ctx.Link (CSharpSiteletsTests "/")),
                        Text "C# Sitelets test minisite"
                    )
                ),
                Elt("li",
                    Elt("a",
                        Attr("href", ctx.Link (CSharpSiteletsTests WebSharper.CSharp.Sitelets.Tests.SiteletTest.JohnDoe)),
                        Text "C# Sitelets test minisite - John Doe"
                    )
                )
            )
        ]
    )

let TestsPage =
    let t12 = (1, 2)
    Content.Page(
        Title = "WebSharper client-side tests",
        Body = [
            ClientSide <@ WebSharper.Tests.Main.RunTests() @>
            ClientSide <@ WebSharper.Collections.Tests.Main.RunTests() @>
            ClientSide <@ WebSharper.Html5.Tests.Main.RunTests() @>
            ClientSide <@ WebSharper.Web.Tests.Main.RunTests() @>
            ClientSide <@ WebSharper.CSharp.Tests.Tests.RunTests() @>
            ClientSide <@ Client.ClientSideTupleTest t12 @>
        ]
    )

let MainSite ctx = function
    | Actions.Home -> HomePage ctx
    | Actions.Tests -> TestsPage

let Main =
    Sitelet.Sum [
        Sitelet.InferPartialInUnion <@ FullAction.Site @> MainSite
        Sitelet.Shift "sitelet-tests" <|
            Sitelet.EmbedInUnion <@ FullAction.SiteletsTests @> SampleSite.EntireSite
        Sitelet.Shift "csharp-tests" <|
            Sitelet.EmbedInUnion <@ FullAction.CSharpSiteletsTests @>
                WebSharper.CSharp.Sitelets.Tests.SiteletTest.Main
    ]
