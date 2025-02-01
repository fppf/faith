type either 'l 'r = | Left 'l, Right 'r |

val is_left x =
  case x {
    Left _ => true,
    Right _ => false,
  }

val is_right x =
  case x {
    Left _ => false,
    Right _ => true,
  }

val map l r x =
  case x {
    Left x => Left (l x),
    Right x => Right (r x),
  }
