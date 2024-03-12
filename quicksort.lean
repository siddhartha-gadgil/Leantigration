import Leantegration.QuickSort

def main (args: List String) : IO Unit := do
  let n := args.head? |>.bind String.toNat? |>.getD 100000
  let m := args[1]? |>.bind String.toNat? |>.getD (n * 10)

  let l ←  List.range n |>.mapM fun _ => IO.rand 0 m

  IO.println s!"Sorting random list of size {n} with max value {m}"
  IO.println "Concurrent, depth 4"
  let start ← IO.monoMsNow
  let sortedArr ←  quickSortConc 4 l
  let done ← IO.monoMsNow
  IO.println s!"Time for sorting: {done - start}ms"
  IO.println s!"Done: got {sortedArr.length} elements. First 10: {sortedArr.take 10}"


  IO.println "Not concurrent"
  let start ← IO.monoMsNow
  let sortedArr := quickSort l
  let done ← IO.monoMsNow
  IO.println s!"Time for sorting: {done - start}ms"
  IO.println s!"Done: got {sortedArr.length} elements. First 10: {sortedArr.take 10}"


  -- IO.println sortedArr
  return ()
