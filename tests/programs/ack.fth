val ack m n =
  if m == 0 then
    n + 1
  else if n == 0 then
    ack (m - 1) 1
  else
    ack (m - 1) (ack m (n - 1))

main = ack 2 5
