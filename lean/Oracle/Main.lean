import MurderMystery
import MurderMystery.Json

/-!
# オラクル

stdin から正規化 JSON を読み、検出結果 JSON を stdout に出す。
入力エラー(§6.4)は stderr にメッセージを出して終了コード 2。
-/
open MurderMystery

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match Lean.Json.parse input >>= Json.parseScenario with
  | .error e =>
    IO.eprintln s!"input error: {e}"
    return 2
  | .ok s =>
    IO.println (Json.output (check s)).pretty
    return 0
