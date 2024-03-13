import Leantegration.QuickSort

def main (args: List String) : IO Unit := do
  let n := args.head? |>.bind String.toNat? |>.getD 100000
  let m := args[1]? |>.bind String.toNat? |>.getD (n * 10)

  let l ←  List.range n |>.mapM fun _ => IO.rand 0 m

  IO.println s!"Sorting random list of size {n} with max value {m}"
  IO.println "Concurrent, depth 5"
  let start ← IO.monoMsNow
  let sortedArr :=  quickSortPar 5 l
  let done ← IO.monoMsNow
  IO.println s!"Time for sorting: {done - start}ms"
  IO.println s!"Done: got {sortedArr.length} elements. First 10: {sortedArr.take 10}"


  IO.println "Not concurrent"
  let start ← IO.monoMsNow
  let sortedArr := quickSort l
  let done ← IO.monoMsNow
  IO.println s!"Time for sorting: {done - start}ms"
  IO.println s!"Done: got {sortedArr.length} elements. First 10: {sortedArr.take 10}"

  let arr := l.toArray
  IO.println "Not concurrent, array"
  let start ← IO.monoMsNow
  let sortedArr := quickSortArr arr
  let done ← IO.monoMsNow
  IO.println s!"Time for sorting: {done - start}ms"
  IO.println s!"Done: got {sortedArr.size} elements. First 10: {sortedArr[0:10]}"

  IO.println "Concurrent, depth 5, array"
  let start ← IO.monoMsNow
  let sortedArr := quickSortArrPar 5 arr
  let done ← IO.monoMsNow
  IO.println s!"Time for sorting: {done - start}ms"
  IO.println s!"Done: got {sortedArr.size} elements. First 10: {sortedArr[0:10]}"

  return ()
