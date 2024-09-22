let test1 i =
  let _ = not true in
  let _ = - i in
  let _ = i + i in
  let _ = i - i in
  let _ = i * i in
  let _ = i / i in
  let _ = i mod i in
  let _ = i == i in
  let _ = i != i in
  let _ = i <= i in
  let _ = i < i in
  let _ = i >= i in
  let _ = i > i in
  let _ = 2 * i + (i + 1) < i in
  let _ = true && true in
  let _ = true || true in
  let _ = true && true || true in
  let _ = true && (true || true) in
  let _ = true || true && true in
  let _ = (true || true) && true in
  ()

let[@warning "-5"] test2 i =
  let _ = (+) in
  let _ = (+) i in
  let _ = (+) i i in
  ()
