try 3 * 
    (try
       (try call_s(3) - call_s(2) + call_s(1)
        with (x1; k1) ->
          let rec h x11 k11 =
            if x11 = 1 then k11 4
            else (fun v -> try k11 v with (x12; k12) -> h x12 k12) (call_s (x11))
          in h x1 k1)
       * 2
     with (x2; k2) ->
       let rec h x21 k21 =
         if x21 = 2 then k21 x21
         else (fun v -> try k21 v with (x22; k22) -> h x22 k22) (call_s (x21))
       in h x2 k2)
with (x3; k3) ->
  let rec h x31 k31 =
    if x31 = 3 then k31 x31
    else (fun v -> try k31 v with (x32; k32) -> h x32 k32) (call_s (x31))
  in h x3 k3



