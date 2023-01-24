module Tests

open Xunit

[<Fact>]
let ``My test`` () =
    Assert.True(true)

[<Fact>]
let ``My test2`` () =
    Assert.True(false)
