import Leantegration.QuickSort

def main : IO Unit := do
  let arr := [3, 2, 1, 5, 4]
  let sortedArr := quickSort arr
  IO.println sortedArr
  return ()
