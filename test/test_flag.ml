let _test_flag = 
  ref true |> Global.register ~name:(__MODULE__ ^ "._test_flag")

let test_flag() = !_test_flag

let enable_tests() = _test_flag:=true
let disable_tests() = _test_flag:=false
