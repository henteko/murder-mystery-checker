import MurderMystery

/-!
# 証明の監査: 主要な定理が依存する公理

`tools/check_axioms.py` がこの出力を読み、標準の公理(propext, Classical.choice, Quot.sound)以外に
依存していないことを確かめる(`exists_valid` だけは `native_decide` を使うので Lean.ofReduceBool も許す)。
定理を足したらここにも足す。
-/
open MurderMystery

-- 定理 1: 健全性・完全性(全体と規則ごと)
#print axioms check_valid
#print axioms check_rule
-- 定理 2: エンディングがちょうど1つ
#print axioms checkG_exactly_one
-- 定理 3: 出力の決定性
#print axioms check_sorted
#print axioms check_nodup
#print axioms check_perm
#print axioms check_perm_events
-- 定理 4: 同時刻イベントの交換可能性
#print axioms reorder_same_time
#print axioms reorder_of_check
#print axioms checkT012_nil_iff
-- 定理 5: 知識の単調性
#print axioms final_knows_of_initial
-- 定理 6: 仕様の無矛盾性
#print axioms exists_valid
-- 定理 7: 導出制約
#print axioms realizable_iff
#print axioms derived_iff
#print axioms tags_sound
-- K010: 探索の被覆の判定
#print axioms coverable_iff
-- 定理 8: 区間の整合
#print axioms segments_consistent
-- 定理 9: 移動時間の決定性
#print axioms edge_unique
#print axioms edgeLookup_eq_some_iff
#print axioms edgeLookup_perm
-- 定理 10: 集計の分割
#print axioms tally_partition
-- 定理 11: 死亡の一意性
#print axioms runAux_dead_stable
