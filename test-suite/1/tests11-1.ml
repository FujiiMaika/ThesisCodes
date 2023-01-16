try call_s (3)
with (x3; k3) ->
  let rec h x31 k31 =
    if x31 = 3 then 1
    else (fun v -> try k31 v with (x32; k32) -> h x32 k32) (call_s (x31))
  in h x3 k3
