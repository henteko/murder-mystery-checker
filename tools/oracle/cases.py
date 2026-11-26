"""手書きのオラクル用テストケースを testdata/oracle/ に書き出す。

各ケースは土台のシナリオ (base.py) を少し変えたもので、入力 JSON の "_case" に
説明 (doc) と、出力に必ず含まれるべきコード (expect) を書く。"_case" はオラクルも Go も無視する。
期待出力 (*.expected.json) は Lean オラクルで作る (make oracle)。

使い方: python3 tools/oracle/cases.py
"""
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(__file__))
from base import base  # noqa: E402

ROOT = os.path.normpath(os.path.join(os.path.dirname(__file__), "..", ".."))
OUT = os.path.join(ROOT, "testdata", "oracle")

CASES = []  # (group, name, doc, expect, scenario dict or raw str)


def case(group, name, doc, expect=()):
    def deco(f):
        s = base()
        r = f(s)
        CASES.append((group, name, doc, list(expect), s if r is None else r))
        return f
    return deco


def ev(s, eid):
    return next(e for e in s["events"] if e["id"] == eid)


def add_events(s, *evs):
    s["events"].extend(evs)


# ---------------------------------------------------------------- R 構造
@case("rules", "R001_duplicate_id", "同じ ID のキャラクターが2人いる", ["R001"])
def _(s):
    s["characters"].append({"id": "alice"})


@case("rules", "R001_gates_other_rules",
      "R001 があれば他の R 規則(ここでは存在しない参照 R002)は出さない", ["R001"])
def _(s):
    s["items"].append({"id": "knife", "initial": {"character": "nobody"}})


@case("rules", "R002_unknown_reference", "イベントが存在しないキャラクターを参照している", ["R002"])
def _(s):
    add_events(s, {"id": "e9", "at": 1290, "kind": "learn", "character": "zed", "facts": ["f_secret"]})


@case("rules", "R003_missing_placement", "初期配置のないキャラクターがいる", ["R003"])
def _(s):
    s["characters"].append({"id": "carol"})


@case("rules", "R004_start_after_end", "開始時刻が終了時刻より後", ["R004"])
def _(s):
    s["start_time"], s["end_time"] = 1320, 1260


@case("rules", "R005_self_edge", "移動時間の表に同じ場所どうしのエントリがある", ["R005"])
def _(s):
    s["travel"] = [{"from": "hall", "to": "hall", "minutes": 1}]


@case("rules", "R005_duplicate_edge", "双方向を展開すると同じ (from, to) が重複する", ["R005"])
def _(s):
    s["travel"] = [{"from": "hall", "to": "study", "minutes": 3, "bidirectional": True},
                   {"from": "study", "to": "hall", "minutes": 4}]


@case("rules", "R006_arrive_before_depart", "move の到着が出発より前", ["R006"])
def _(s):
    ev(s, "e1")["arrive"] = 1265


@case("rules", "R006_self_transfer", "自分に物を渡している", ["R006"])
def _(s):
    ev(s, "e3")["to"] = "alice"


@case("rules", "R007_clue_nowhere", "手がかりに場所もアイテムも山札もない", ["R007"])
def _(s):
    s["clues"] = [{"id": "c1", "reveals": ["f_secret"]}]


@case("rules", "R008_empty_values", "列挙型の選択の値が空", ["R008"])
def _(s):
    s["choices"].append({"id": "c_empty", "owner": "alice", "values": []})


@case("rules", "R009_var_on_enum", "列挙型の選択を真偽値として使っている", ["R009"])
def _(s):
    s["constraints"] = [{"var": "c_vote"}]


@case("rules", "R010_true_fact_refuted", "真の知識が contradicted_by を持つ", ["R010"])
def _(s):
    s["facts"][0]["contradicted_by"] = ["f_meeting"]


@case("rules", "R011_about_without_claimed_at", "証言に about があるのに claimed_at がない", ["R011"])
def _(s):
    s["facts"].append({"id": "f_claim", "about": {"event": "e1"}})


@case("rules", "R012_empty_votes", "plurality の votes が空", ["R012"])
def _(s):
    s["endings"][0]["condition"] = {"plurality": {"votes": [], "value": "alice"}}


@case("rules", "R013_assertion_out_of_range", "断言の時刻が終了時刻ちょうど(範囲外)", ["R013"])
def _(s):
    s["assertions"] = [{"id": "a1", "kind": "present", "location": "hall", "at": 1320, "characters": ["alice"]}]


# ---------------------------------------------------------------- T タイムライン
@case("rules", "T001_event_after_end", "イベントの時刻が終了時刻より後", ["T001"])
def _(s):
    add_events(s, {"id": "e9", "at": 1330, "kind": "learn", "character": "alice", "facts": ["f_meeting"]})


@case("rules", "T002_no_route", "徒歩で経路のない場所へ移動している", ["T002"])
def _(s):
    s["locations"].append({"id": "garden"})
    add_events(s, {"id": "e9", "at": 1290, "kind": "move", "character": "alice", "to": "garden", "arrive": 1300})


@case("rules", "T003_too_fast", "移動時間 5 分のところを 2 分で着いている", ["T003"])
def _(s):
    ev(s, "e1")["arrive"] = 1272


@case("rules", "T004_move_to_same_place", "今いる場所へ移動している", ["T004"])
def _(s):
    add_events(s, {"id": "e9", "at": 1262, "kind": "move", "character": "alice", "to": "hall", "arrive": 1265})


@case("rules", "T005_two_events_same_time", "alice が同じ時刻に2つのイベントに参加している", ["T005"])
def _(s):
    add_events(s, {"id": "e9", "at": 1285, "kind": "learn", "character": "alice", "facts": ["f_meeting"]})


@case("rules", "T006_act_while_moving", "移動中の bob が行動している", ["T006"])
def _(s):
    add_events(s, {"id": "e9", "at": 1272, "kind": "learn", "character": "bob", "facts": ["f_secret"]})


@case("rules", "T007_not_at_scene", "場面の参加者がその場所にいない", ["T007"])
def _(s):
    add_events(s, {"id": "e9", "at": 1265, "kind": "scene", "location": "hall", "participants": ["alice", "bob"]})


@case("rules", "T008_transfer_apart", "別の場所にいる2人の間で物を渡している", ["T008"])
def _(s):
    ev(s, "e3")["at"] = 1265


@case("rules", "T009_unacknowledged_encounter", "2人が同じ部屋にいたのに、互いに気づいた記述がない", ["T009"])
def _(s):
    s["events"] = [ev(s, "e1")]


@case("rules", "T010_act_after_death", "死亡した alice が行動している", ["T010"])
def _(s):
    add_events(s, {"id": "e0", "at": 1282, "kind": "die", "character": "alice"})


@case("rules", "T011_cannot_perceive", "知覚の表にない場所を観察している", ["T011"])
def _(s):
    add_events(s, {"id": "e9", "at": 1265, "kind": "observe", "character": "alice", "location": "hall",
                   "target_location": "study", "targets": ["bob"], "facts": ["f_meeting"]})


@case("rules", "T012_observed_target_departs", "観察される bob が同じ時刻に移動を始めている", ["T012"])
def _(s):
    s["placements"][1]["location"] = "hall"
    s["events"] = [
        {"id": "a_look", "at": 1270, "kind": "observe", "character": "alice", "location": "hall",
         "targets": ["bob"], "facts": ["f_meeting"]},
        {"id": "b_leave", "at": 1270, "kind": "move", "character": "bob", "to": "study", "arrive": 1275},
    ]


# ---------------------------------------------------------------- I 所持品
@case("rules", "I001_give_not_held", "持っていない物を渡している", ["I001"])
def _(s):
    ev(s, "e3")["from"], ev(s, "e3")["to"] = "bob", "alice"


@case("rules", "I002_use_consumed", "使い切った物を使っている", ["I002"])
def _(s):
    add_events(s, {"id": "e8", "at": 1290, "kind": "consume", "character": "bob", "item": "knife"},
               {"id": "e9", "at": 1295, "kind": "use", "character": "bob", "item": "knife"})


@case("rules", "I003_pickup_elsewhere", "その場所にない物を拾っている", ["I003"])
def _(s):
    s["items"].append({"id": "key", "initial": {"location": "study"}})
    add_events(s, {"id": "e9", "at": 1290, "kind": "pickup", "character": "alice", "item": "key"})


@case("rules", "I004_same_item_same_time", "同じ時刻に同じ物を2つのイベントで扱っている(扱う人が重なるので T005 も出る)", ["I004", "T005"])
def _(s):
    add_events(s, {"id": "e4", "at": 1285, "kind": "use", "character": "bob", "item": "knife"})


# ---------------------------------------------------------------- K 知識・手がかり
@case("rules", "K001_tell_unknown", "知らないことを話している", ["K001"])
def _(s):
    add_events(s, {"id": "e9", "at": 1290, "kind": "tell", "from": "bob", "to": "alice", "facts": ["f_secret"]})


@case("rules", "K002_missing_requirement", "行動に必要な知識を持っていない", ["K002"])
def _(s):
    ev(s, "e3")["requires"] = ["f_secret"]
    ev(s, "e3")["from"], ev(s, "e3")["to"] = "alice", "bob"
    s["initial_knowledge"] = []
    s["solution_facts"] = []


@case("rules", "K003_unobtainable_solution", "真相に必要な知識がプレイヤーに手に入らない", ["K003"])
def _(s):
    s["facts"].append({"id": "f_hidden"})
    s["solution_facts"].append("f_hidden")


@case("rules", "K004_clue_consumed", "手がかりの物が使い切られている", ["K004"])
def _(s):
    s["clues"] = [{"id": "c_knife", "item": "knife", "reveals": ["f_secret"]}]
    add_events(s, {"id": "e9", "at": 1290, "kind": "consume", "character": "bob", "item": "knife"})


@case("rules", "K005_clue_misplaced", "手がかりの物が書かれた場所にない", ["K005"])
def _(s):
    s["clues"] = [{"id": "c_knife", "item": "knife", "location": "study", "reveals": ["f_secret"]}]


@case("rules", "K006_lie_cannot_be_refuted", "偽の知識を否定する手段がプレイヤーにない", ["K006"])
def _(s):
    s["facts"].append({"id": "f_lie", "truth": False, "contradicted_by": ["f_truth"]})
    s["facts"].append({"id": "f_truth"})
    s["initial_knowledge"].append({"character": "bob", "fact": "f_lie"})


@case("rules", "K007_solution_depends_on_lie", "真相が偽の知識に依存している", ["K007"])
def _(s):
    s["facts"].append({"id": "f_lie", "truth": False, "contradicted_by": ["f_meeting"]})
    s["initial_knowledge"].append({"character": "alice", "fact": "f_lie"})
    s["solution_facts"].append("f_lie")


@case("rules", "K009_leftover_cards", "探索で引ける枚数(1人1枚 × 2人)より探索カードが多い(警告)", ["K009"])
def _(s):
    s["facts"].append({"id": "f_extra"})
    s["clues"] = [{"id": f"x{k}", "deck": "d", "reveals": ["f_extra"]} for k in range(3)]
    s["exploration"] = {"draws_per_player": 1}


@case("rules", "K010_cannot_draw_truth",
      "真相の知識が2枚の手がかりにしかないのに、探索で1枚しか引けない", ["K010"])
def _(s):
    s["initial_knowledge"] = []
    s["facts"].append({"id": "f_motive"})
    s["solution_facts"] = ["f_secret", "f_motive"]
    s["clues"] = [{"id": "x_secret", "deck": "d", "reveals": ["f_secret"]},
                  {"id": "x_motive", "deck": "d", "reveals": ["f_motive"]}]
    s["characters"].append({"id": "victim", "npc": True})
    s["placements"].append({"character": "victim", "location": "study"})
    s["initial_knowledge"] = [{"character": "victim", "fact": "f_secret"}]
    s["exploration"] = {"draws_per_player": 1}
    s["characters"] = [c for c in s["characters"]]
    # プレイヤー2人 × 1枚 = 2枚なら足りるので、alice だけをプレイヤーにする
    s["characters"] = [{"id": "alice"}, {"id": "bob", "npc": True}, {"id": "victim", "npc": True}]
    s["goals"] = [{"id": "g_alice", "owner": "alice"}]
    s["choices"][0]["owner"] = "alice"


@case("rules", "K010_round_capacity",
      "真相のカード2枚は1回目にしか引けないが、1回目は1枚しか引けない(合計の枚数は足りる)", ["K010"])
def _(s):
    s["facts"] += [{"id": "f_motive"}, {"id": "f_extra"}]
    s["solution_facts"] = ["f_secret", "f_motive"]
    s["clues"] = [{"id": "x_secret", "deck": "d", "reveals": ["f_secret"]},
                  {"id": "x_motive", "deck": "d", "reveals": ["f_motive"]},
                  {"id": "x_other", "deck": "d", "reveals": ["f_extra"]}]
    s["characters"] = [{"id": "alice"}, {"id": "bob", "npc": True}]
    s["initial_knowledge"] = []
    s["goals"] = [{"id": "g_alice", "owner": "alice"}]
    s["choices"][0]["owner"] = "alice"
    s["exploration"] = {"rounds": [{"draws_per_player": 1, "clues": ["x_secret", "x_motive"]},
                                   {"draws_per_player": 2, "clues": ["x_other"]}]}


@case("rules", "K011_card_never_drawable", "どの回でも引けない探索カードがある(警告)", ["K011"])
def _(s):
    s["facts"].append({"id": "f_extra"})
    s["clues"] = [{"id": "x0", "deck": "d", "reveals": ["f_extra"]},
                  {"id": "x1", "deck": "d", "reveals": ["f_extra"]}]
    s["exploration"] = {"rounds": [{"draws_per_player": 1, "clues": ["x0"]}]}


@case("rules", "R002_round_unknown_clue", "探索の回の clues が存在しない探索カードを参照している", ["R002"])
def _(s):
    s["facts"].append({"id": "f_extra"})
    s["clues"] = [{"id": "x0", "deck": "d", "reveals": ["f_extra"]}]
    s["exploration"] = {"rounds": [{"draws_per_player": 1, "clues": ["x0", "ghost"]}]}


@case("rules", "K008_claim_time_off", "証言は 1260 と言うが、実際の移動は 1270", ["K008"])
def _(s):
    s["facts"].append({"id": "f_claim", "about": {"event": "e1"}, "claimed_at": 1260})


# ---------------------------------------------------------------- H ハンドアウト・盤面
@case("rules", "H001_handout_location", "ハンドアウトの居場所が終了時の居場所と違う", ["H001"])
def _(s):
    s["handouts"] = [{"character": "bob", "location": "study"}]


@case("rules", "H002_handout_item_missing", "ハンドアウトの持ち物を実際には持っていない", ["H002"])
def _(s):
    s["handouts"] = [{"character": "alice", "items": ["knife"]}]


@case("rules", "H003_handout_item_unlisted", "持っている物がハンドアウトに書かれていない(警告)", ["H003"])
def _(s):
    s["handouts"] = [{"character": "bob", "items": []}]


@case("rules", "H004_handout_impossible_knowledge", "ハンドアウトに知りえない情報が書かれている", ["H004"])
def _(s):
    s["handouts"] = [{"character": "bob", "knows": ["f_secret", "f_meeting"]}]


@case("rules", "H005_handout_knowledge_unlisted", "知っている情報がハンドアウトに書かれていない(警告)", ["H005"])
def _(s):
    s["handouts"] = [{"character": "alice", "knows": ["f_meeting"]}]


@case("rules", "H006_board_item_missing", "盤面に置いた物が実際にはそこにない", ["H006"])
def _(s):
    s["board"] = [{"location": "study", "items": ["knife"]}]


@case("rules", "H007_board_item_unlisted", "その場所にある物が盤面に書かれていない(警告)", ["H007"])
def _(s):
    s["items"].append({"id": "vase", "initial": {"location": "study"}})
    s["board"] = [{"location": "study", "items": []}]


# ---------------------------------------------------------------- A 断言
@case("rules", "A001_assertion_contradicted", "断言「1290 に alice は hall にいない」がタイムラインと矛盾", ["A001"])
def _(s):
    s["assertions"] = [{"id": "a1", "kind": "absent", "location": "hall", "at": 1290, "characters": ["alice"]}]


# ---------------------------------------------------------------- G ゴール・エンディング
@case("rules", "G001_no_ending", "c_vote = bob のときどのエンディングにもならない", ["G001"])
def _(s):
    s["endings"] = s["endings"][:1]


@case("rules", "G002_two_endings", "c_vote = alice のとき2つのエンディングが成り立つ", ["G002"])
def _(s):
    s["endings"].append({"id": "end_c", "condition": {"eq": {"var": "c_vote", "value": "alice"}}})


@case("rules", "G003_unreachable_ending", "どう選んでも到達しないエンディングがある", ["G003"])
def _(s):
    s["endings"].append({"id": "end_never", "condition": {"const": False}})


@case("rules", "G004_impossible_goal", "制約により g_alice が達成できない", ["G004"])
def _(s):
    s["constraints"] = [{"not": {"var": "g_alice"}}]


@case("rules", "G005_contradictory_constraints", "制約が矛盾していて選び方が1つもない", ["G005"])
def _(s):
    s["constraints"] = [{"const": False}]


@case("rules", "G006_goal_always_true", "g_alice が必ず達成される(警告)", ["G006"])
def _(s):
    s["constraints"] = [{"var": "g_alice"}]


@case("rules", "G007_too_many_patterns", "選び方の組み合わせが 2^20 を超える", ["G007"])
def _(s):
    s["choices"] += [{"id": f"c_flag{i:02d}", "owner": "alice"} for i in range(20)]


@case("rules", "G008_character_without_goal", "ゴールを持たないプレイヤーキャラクターがいる(警告)", ["G008"])
def _(s):
    s["characters"].append({"id": "carol"})
    s["locations"].append({"id": "kitchen", "area": "house"})
    s["placements"].append({"character": "carol", "location": "kitchen"})


@case("rules", "G009_value_never_chosen", "制約により c_vote = carol が選ばれることがない(警告)", ["G009"])
def _(s):
    s["choices"][0]["values"] = ["alice", "bob", "carol"]
    s["endings"][1]["condition"] = {"not": {"eq": {"var": "c_vote", "value": "alice"}}}
    s["constraints"] = [{"not": {"eq": {"var": "c_vote", "value": "carol"}}}]


# ---------------------------------------------------------------- 境界・意味論
@case("edge", "clean_base", "土台のシナリオ。検出結果は 0 件")
def _(s):
    pass


@case("edge", "integral_number_forms", "整数値なら 1270.0 や 1.275e3 の表記も受け付ける(§6.4)")
def _(s):
    ev(s, "e1")["at"] = 1270.0
    ev(s, "e1")["arrive"] = 1.275e3


@case("edge", "no_variables_no_endings",
      "ゴールも選択もエンディングもない。空の割り当て1通りでエンディングがないので G001(witness は空)", ["G001"])
def _(s):
    s["goals"], s["choices"], s["endings"] = [], [], []
    s["characters"] = [{"id": "alice", "npc": True}, {"id": "bob", "npc": True}]


@case("edge", "fall_skips_travel_time", "mode が fall の移動は移動時間を検査しない")
def _(s):
    ev(s, "e1")["mode"] = "fall"
    ev(s, "e1")["arrive"] = 1270


@case("edge", "fatal_move_then_act", "fatal な移動の後に行動すると T010", ["T010"])
def _(s):
    ev(s, "e1")["fatal"] = True
    ev(s, "e1")["mode"] = "fall"


@case("edge", "remote_observe_with_perception", "知覚の表があれば離れた場所を観察できる")
def _(s):
    s["perception"] = [{"from": "hall", "to": "study"}]
    s["events"].insert(0, {"id": "e0", "at": 1265, "kind": "observe", "character": "alice", "location": "hall",
                           "target_location": "study", "targets": ["bob"], "facts": ["f_meeting"]})


@case("edge", "explicit_travel_overrides_area", "travel の表がエリア内の移動時間より優先される", ["T003"])
def _(s):
    s["travel"] = [{"from": "study", "to": "hall", "minutes": 10}]


@case("edge", "area_travel", "エリア間の移動時間を使う", ["T003"])
def _(s):
    s["areas"].append({"id": "yard"})
    s["locations"].append({"id": "garden", "area": "yard"})
    s["area_travel"] = [{"from": "house", "to": "yard", "minutes": 8, "bidirectional": True}]
    add_events(s, {"id": "e9", "at": 1290, "kind": "move", "character": "alice", "to": "garden", "arrive": 1295})


@case("edge", "T005_reports_last_only", "同時刻の前のイベントが2つあっても、T005 は直前の1件についてだけ出る(e4 は e3 と、e5 は e4 とだけ)", ["T005"])
def _(s):
    s["characters"].append({"id": "carol"})
    s["placements"].append({"character": "carol", "location": "hall"})
    s["goals"].append({"id": "g_carol", "owner": "carol"})
    ev(s, "e2")["participants"].append("carol")
    add_events(s, {"id": "e4", "at": 1285, "kind": "learn", "character": "alice", "facts": ["f_meeting"]},
               {"id": "e5", "at": 1285, "kind": "learn", "character": "alice", "facts": ["f_meeting"]})


@case("edge", "npc_knowledge_not_obtainable", "NPC だけが知っている知識は入手可能ではない", ["K003"])
def _(s):
    s["characters"].append({"id": "butler", "npc": True})
    s["locations"].append({"id": "kitchen", "area": "house"})
    s["placements"].append({"character": "butler", "location": "kitchen"})
    s["facts"].append({"id": "f_npc"})
    s["initial_knowledge"].append({"character": "butler", "fact": "f_npc"})
    s["solution_facts"].append("f_npc")


@case("edge", "clue_deck_makes_obtainable", "山札の手がかりで知識が入手可能になる")
def _(s):
    s["facts"].append({"id": "f_card"})
    s["solution_facts"].append("f_card")
    s["clues"] = [{"id": "c1", "deck": "about_alice", "reveals": ["f_card"]}]


@case("edge", "K008_arrive_point_with_tolerance", "到着時刻を指す証言は tolerance の範囲内なら出ない")
def _(s):
    s["facts"].append({"id": "f_claim", "about": {"event": "e1", "point": "arrive"}, "claimed_at": 1277,
                       "tolerance": 2})


@case("edge", "false_claim_not_checked", "偽の証言は時刻がずれていても K008 の対象外")
def _(s):
    s["facts"].append({"id": "f_claim", "truth": False, "about": {"event": "e1"}, "claimed_at": 1200,
                       "contradicted_by": ["f_meeting"]})


@case("edge", "derived_constraint_consumed", "requires_items のアイテムが失われたゴールは達成できない(導出制約)", ["G004"])
def _(s):
    s["goals"][0]["requires_items"] = ["knife"]
    add_events(s, {"id": "e9", "at": 1290, "kind": "consume", "character": "bob", "item": "knife"})


@case("edge", "derived_constraint_clash",
      "owner の違うゴールが同じアイテムを要求すると同時に達成できない(導出制約)。両方達成のエンディングは G003", ["G003"])
def _(s):
    s["goals"][0]["requires_items"] = ["knife"]
    s["goals"][1]["requires_items"] = ["knife"]
    s["endings"] = [
        {"id": "end_both", "condition": {"and": [{"var": "g_alice"}, {"var": "g_bob"}]}},
        {"id": "end_other", "condition": {"not": {"and": [{"var": "g_alice"}, {"var": "g_bob"}]}}},
    ]


@case("edge", "goal_knowledge_unobtainable",
      "requires_knowledge の知識が入手可能でないゴールは達成できない(導出制約 3)", ["G004"])
def _(s):
    s["facts"].append({"id": "f_hidden"})
    s["goals"][0]["requires_knowledge"] = ["f_hidden"]


@case("edge", "goal_knowledge_obtainable", "requires_knowledge の知識をプレイヤーが知っていれば達成できる")
def _(s):
    s["goals"][0]["requires_knowledge"] = ["f_meeting", "f_secret"]


@case("edge", "goal_knowledge_via_clue", "手がかりで明かされる知識も入手可能")
def _(s):
    s["facts"].append({"id": "f_hidden"})
    s["clues"] = [{"id": "x_hidden", "deck": "study", "reveals": ["f_hidden"]}]
    s["goals"][0]["requires_knowledge"] = ["f_hidden"]


@case("edge", "goal_knowledge_npc_only", "NPC だけが知っている知識は入手可能ではない", ["G004"])
def _(s):
    s["characters"].append({"id": "victim", "npc": True})
    s["placements"].append({"character": "victim", "location": "study"})
    s["facts"].append({"id": "f_hidden"})
    s["initial_knowledge"].append({"character": "victim", "fact": "f_hidden"})
    s["goals"][0]["requires_knowledge"] = ["f_hidden"]


@case("edge", "goal_condition", "condition でゴールと投票を結ぶ(ゴール ⇔ alice に投票)")
def _(s):
    s["goals"][0]["condition"] = {"eq": {"var": "c_vote", "value": "alice"}}


@case("edge", "goal_condition_false", "condition が常に偽のゴールは達成できない", ["G004"])
def _(s):
    s["goals"][0]["condition"] = {"const": False}


@case("edge", "goal_condition_true", "condition が常に真のゴールは必ず達成される(警告)", ["G006"])
def _(s):
    s["goals"][0]["condition"] = {"const": True}


@case("edge", "goal_condition_vs_items",
      "condition が真でも requires_items のアイテムが失われていれば、その選び方はパターンにならない(alice への投票がなくなる)",
      ["G003", "G004", "G006", "G009"])
def _(s):
    s["goals"][0]["condition"] = {"eq": {"var": "c_vote", "value": "alice"}}
    s["goals"][0]["requires_items"] = ["knife"]
    add_events(s, {"id": "e9", "at": 1290, "kind": "consume", "character": "bob", "item": "knife"})


@case("edge", "goal_condition_unknown_var", "condition が存在しない変数を参照している", ["R002"])
def _(s):
    s["goals"][0]["condition"] = {"var": "c_nothing"}


@case("edge", "goal_condition_type_error", "condition が列挙型の選択を真偽値として使っている", ["R009"])
def _(s):
    s["goals"][0]["condition"] = {"var": "c_vote"}


@case("edge", "goal_knowledge_unknown_fact", "requires_knowledge が存在しない知識を参照している", ["R002"])
def _(s):
    s["goals"][0]["requires_knowledge"] = ["f_nothing"]


@case("edge", "exploration_enough", "探索で引ける枚数で真相の手がかりを引き切れる(1枚に2つの知識)")
def _(s):
    s["initial_knowledge"] = []
    s["facts"].append({"id": "f_motive"})
    s["solution_facts"] = ["f_secret", "f_motive"]
    s["clues"] = [{"id": "x_both", "deck": "d", "reveals": ["f_secret", "f_motive"]}]
    s["exploration"] = {"draws_per_player": 1}


@case("edge", "exploration_known_by_player",
      "プレイヤーが知っている真相の知識はカードを引かなくてよい(K010 なし。0枚しか引けないので K009 と K011 は出る)", ["K009", "K011"])
def _(s):
    s["clues"] = [{"id": "x_secret", "deck": "d", "reveals": ["f_secret"]}]
    s["exploration"] = {"draws_per_player": 0}


@case("edge", "exploration_rounds_enough",
      "真相のカードを1回目と2回目に1枚ずつ引ける(K010 なし)")
def _(s):
    s["facts"] += [{"id": "f_motive"}, {"id": "f_extra"}]
    s["solution_facts"] = ["f_secret", "f_motive"]
    s["clues"] = [{"id": "x_secret", "deck": "d", "reveals": ["f_secret"]},
                  {"id": "x_motive", "deck": "d", "reveals": ["f_motive"]},
                  {"id": "x_other", "deck": "d", "reveals": ["f_extra"]}]
    s["characters"] = [{"id": "alice"}, {"id": "bob", "npc": True}]
    s["initial_knowledge"] = []
    s["goals"] = [{"id": "g_alice", "owner": "alice"}]
    s["choices"][0]["owner"] = "alice"
    s["exploration"] = {"rounds": [{"draws_per_player": 1, "clues": ["x_secret", "x_motive"]},
                                   {"draws_per_player": 2, "clues": ["x_motive", "x_other"]}]}


@case("edge", "exploration_round_zero_draws",
      "カードを引けるのが、1人0枚の回だけ(K011。真相はプレイヤーが知っているので K010 なし)", ["K011"])
def _(s):
    s["clues"] = [{"id": "x_a", "deck": "d", "reveals": ["f_meeting"]}]
    s["exploration"] = {"rounds": [{"draws_per_player": 0, "clues": ["x_a"]}, {"draws_per_player": 1, "clues": []}]}


@case("edge", "extra_fields_allowed", "note、_ で始まるキー、説明の name / text はどこにでも置ける(検出なし)")
def _(s):
    s["note"] = "メモ"
    s["_meta"] = {"anything": [1, 2]}
    s["characters"][0]["name"] = "アリス"
    s["characters"][1]["note"] = "x"
    s["facts"][0]["text"] = "秘密"
    s["events"][0]["name"] = "移動"
    s["events"][0]["_src"] = 3
    s["endings"][0]["name"] = "A"
    s["clues"] = [{"id": "x0", "deck": "d", "reveals": ["f_meeting"], "name": "カード", "text": "本文"}]
    s["exploration"] = {"rounds": [{"draws_per_player": 1, "name": "調査 1", "note": "現場のみ"}]}


@case("edge", "tagged_items", "タグのアイテムを2つ持つゴール。使えるアイテムが1つしかないと達成できない", ["G004"])
def _(s):
    s["items"] = [{"id": "knife", "initial": {"character": "alice"}, "tags": ["private_alice"]},
                  {"id": "ring", "initial": {"location": "hall"}, "tags": ["private_alice"]}]
    s["goals"][1]["requires_tagged"] = [{"tag": "private_alice", "count": 2}]
    add_events(s, {"id": "e9", "at": 1290, "kind": "consume", "character": "bob", "item": "knife"})


@case("edge", "tagged_items_ok", "タグのアイテムが2つ残っていれば達成できる")
def _(s):
    s["items"] = [{"id": "knife", "initial": {"character": "alice"}, "tags": ["private_alice"]},
                  {"id": "ring", "initial": {"location": "hall"}, "tags": ["private_alice"]}]
    s["goals"][1]["requires_tagged"] = [{"tag": "private_alice", "count": 2}]


@case("edge", "tagged_clash",
      "2人がタグのアイテムを取り合い、合わせた数が足りないと同時には達成できない。両方達成のエンディングは G003", ["G003"])
def _(s):
    s["items"] = [{"id": "knife", "initial": {"character": "alice"}, "tags": ["shiny"]},
                  {"id": "ring", "initial": {"location": "hall"}, "tags": ["shiny"]}]
    s["goals"][0]["requires_tagged"] = [{"tag": "shiny", "count": 1}]
    s["goals"][1]["requires_tagged"] = [{"tag": "shiny", "count": 2}]
    s["endings"] = [
        {"id": "end_both", "condition": {"and": [{"var": "g_alice"}, {"var": "g_bob"}]}},
        {"id": "end_other", "condition": {"not": {"and": [{"var": "g_alice"}, {"var": "g_bob"}]}}},
    ]


@case("edge", "conceals_exposed", "隠したい知識をほかのプレイヤーがすでに知っていると達成できない", ["G004"])
def _(s):
    s["goals"][1]["conceals"] = ["f_meeting"]


@case("edge", "conceals_ok", "隠したい知識を本人しか知らなければ達成できる")
def _(s):
    s["goals"][0]["conceals"] = ["f_secret"]


@case("edge", "truth_condition", "真相によって分かれる条件: f_secret が真なので alice への投票で達成")
def _(s):
    s["goals"][0]["condition"] = {"or": [
        {"and": [{"truth": "f_secret"}, {"eq": {"var": "c_vote", "value": "alice"}}]},
        {"and": [{"not": {"truth": "f_secret"}}, {"eq": {"var": "c_vote", "value": "bob"}}]}]}


@case("edge", "truth_false_fact", "偽の知識の truth は偽。常に偽の条件のゴールは達成できない", ["G004"])
def _(s):
    s["facts"].append({"id": "f_lie", "truth": False, "contradicted_by": ["f_meeting"]})
    s["goals"][0]["condition"] = {"truth": "f_lie"}


@case("edge", "truth_unknown_fact", "truth が存在しない知識を参照している", ["R002"])
def _(s):
    s["goals"][0]["condition"] = {"truth": "f_nothing"}


@case("edge", "plurality_and_tie", "plurality と tie でエンディングを分ける。どの票でもちょうど1つ")
def _(s):
    s["choices"] = [{"id": "v_alice", "owner": "alice", "values": ["alice", "bob"]},
                    {"id": "v_bob", "owner": "bob", "values": ["alice", "bob"]}]
    votes = ["v_alice", "v_bob"]
    s["endings"] = [
        {"id": "end_a", "condition": {"plurality": {"votes": votes, "value": "alice"}}},
        {"id": "end_b", "condition": {"plurality": {"votes": votes, "value": "bob"}}},
        {"id": "end_tie", "condition": {"tie": {"votes": votes}}},
    ]


@case("edge", "G001_minimal_witness", "G001 の witness は割り当ての順序で最小のもの", ["G001"])
def _(s):
    s["endings"] = [{"id": "end_x", "condition": {"and": [{"var": "g_alice"}, {"var": "g_bob"}]}}]


@case("edge", "R_gates_content_rules", "R の違反があれば T 群などは出さない", ["R002"])
def _(s):
    ev(s, "e1")["arrive"] = 1272          # T003 になるはずだが出ない
    s["solution_facts"].append("f_unknown")


@case("edge", "assertion_at_departure_minute", "出発した時刻ちょうどは移動中。断言「1270 に bob は study にいない」は成り立つ")
def _(s):
    s["assertions"] = [{"id": "a1", "kind": "absent", "location": "study", "at": 1270, "characters": ["bob"]}]


@case("edge", "dead_is_not_present", "死亡後の時刻の居場所は dead。present の断言は A001", ["A001"])
def _(s):
    add_events(s, {"id": "e9", "at": 1290, "kind": "die", "character": "bob"})
    s["assertions"] = [{"id": "a1", "kind": "present", "location": "hall", "at": 1300, "characters": ["bob"]}]


# ---------------------------------------------------------------- 反例の回帰テスト (docs/PROOFS.md)
def _t012(obs_id):
    def f(s):
        s["placements"][1]["location"] = "hall"
        s["events"] = [
            {"id": obs_id, "at": 1270, "kind": "observe", "character": "alice", "location": "hall",
             "targets": ["bob"], "facts": ["f_meeting"]},
            {"id": "m_leave", "at": 1270, "kind": "move", "character": "bob", "to": "study", "arrive": 1275},
        ]
    return f


case("regress", "cx3_observe_first", "反例3: 観察の ID が先(a_)。T007 は出ず、T012 だけ出る", ["T012"])(_t012("a_look"))
case("regress", "cx3_move_first", "反例3: 観察の ID が後(z_)。T007 と T012 が出る", ["T007", "T012"])(_t012("z_look"))


def _dup_event(rev):
    def f(s):
        s["facts"].append({"id": "f_arrive", "about": {"event": "e1", "point": "arrive"}, "claimed_at": 1275})
        dup = {"id": "e1", "at": 1290, "kind": "learn", "character": "alice", "facts": ["f_meeting"]}
        if rev:
            s["events"].insert(0, dup)
        else:
            s["events"].append(dup)
    return f


case("regress", "cx2_dup_event_order_a", "反例2: ID の重複したイベントの順 A。R001 だけ出る", ["R001"])(_dup_event(False))
case("regress", "cx2_dup_event_order_b", "反例2: 順 B。出力は順 A と同じ", ["R001"])(_dup_event(True))


def _dup_fact(rev):
    def f(s):
        pair = [{"id": "x", "truth": True}, {"id": "x", "truth": False}]
        s["facts"] += (pair[::-1] if rev else pair) + [{"id": "f_lie", "truth": False, "contradicted_by": ["x"]}]
    return f


case("regress", "cx5_dup_fact_order_a", "反例5: 同じ ID の真偽の知識の順 A。R001 だけ出る", ["R001"])(_dup_fact(False))
case("regress", "cx5_dup_fact_order_b", "反例5: 順 B。出力は順 A と同じ", ["R001"])(_dup_fact(True))


def _dup_choice(rev):
    def f(s):
        pair = [{"id": "c_x", "owner": "alice"}, {"id": "c_x", "owner": "alice", "values": ["p", "q"]}]
        s["choices"] += pair[::-1] if rev else pair
        s["constraints"] = [{"var": "c_x"}]
    return f


case("regress", "cx5_dup_choice_order_a", "反例5: 同じ ID の選択の順 A。R001 だけ出る", ["R001"])(_dup_choice(False))
case("regress", "cx5_dup_choice_order_b", "反例5: 順 B。出力は順 A と同じ", ["R001"])(_dup_choice(True))


@case("regress", "cx4_other_departs_during_scene",
      "反例4: 1290 に alice だけの場面、同じ 1290 に場面に参加しない bob が移動を始める。"
      "場面の処理前の状態では bob はまだ hall だが、1290 の居場所は移動中。検出結果は 0 件")
def _(s):
    s["events"].append({"id": "e4", "at": 1290, "kind": "scene", "location": "hall", "participants": ["alice"]})
    s["events"].append({"id": "e5", "at": 1290, "kind": "move", "character": "bob", "to": "study", "arrive": 1295})
    s["assertions"] = [{"id": "a1", "kind": "absent", "location": "hall", "at": 1290, "characters": ["bob"]}]


# ---------------------------------------------------------------- 入力エラー (§6.4)
SCHEMA = [
    ("invalid_json", "JSON として不正", '{"start_time": 1260,'),
    ("missing_characters", "必須フィールド characters がない", None),
    ("string_time", "時刻が文字列", None),
    ("negative_time", "時刻が負", None),
    ("fractional_time", "時刻が整数でない(1260.5)", None),
    ("huge_exponent", "指数部が 100,000 を超える(値は 0 でも入力エラー)", '{"start_time": 0e100001, "end_time": 1320, '
     '"characters": [], "locations": [], "placements": []}'),
    ("duplicate_key", "同じキーが2回ある", '{"start_time": 1260, "start_time": 1261, "end_time": 1320, '
     '"characters": [], "locations": [], "placements": []}'),
    ("time_out_of_range", "時刻が上限を超える", None),
    ("unknown_event_kind", "未知のイベントの種類", None),
    ("empty_id", "ID が空文字列", None),
    ("initial_both", "initial が character と location の両方を持つ", None),
    ("formula_two_keys", "論理式のオブジェクトにキーが2つある", None),
    ("unknown_assertion_kind", "未知の断言の種類", None),
    ("unknown_field_top", "トップレベルに知らないキーがある (0.8.0)", None),
    ("unknown_field_typo", "move に知らないキー(targets のつもりの target)がある", None),
    ("field_of_other_kind", "scene に move のキー to がある", None),
    ("exploration_both", "exploration に draws_per_player と rounds の両方がある", None),
    ("exploration_neither", "exploration に draws_per_player も rounds もない", None),
    ("exploration_rounds_empty", "rounds が空", None),
    ("exploration_round_unknown_field", "回に知らないキー(draws_per_player のつもりの draws)がある", None),
]


def schema_case(name):
    s = base()
    if name == "missing_characters":
        del s["characters"]
    elif name == "string_time":
        s["start_time"] = "1260"
    elif name == "negative_time":
        s["events"][0]["at"] = -1
    elif name == "fractional_time":
        s["events"][0]["at"] = 1270.5
    elif name == "time_out_of_range":
        s["end_time"] = 10000001
    elif name == "unknown_event_kind":
        s["events"][0]["kind"] = "teleport"
    elif name == "empty_id":
        s["characters"][0]["id"] = ""
    elif name == "initial_both":
        s["items"][0]["initial"] = {"character": "alice", "location": "hall"}
    elif name == "formula_two_keys":
        s["endings"][0]["condition"] = {"var": "g_alice", "const": True}
    elif name == "unknown_assertion_kind":
        s["assertions"] = [{"id": "a1", "kind": "maybe", "location": "hall", "at": 1270, "characters": ["alice"]}]
    elif name == "unknown_field_top":
        s["phases"] = [{"kind": "discussion"}, {"kind": "exploration", "draws": 1}]
    elif name == "unknown_field_typo":
        s["events"][0]["target"] = "x"
    elif name == "field_of_other_kind":
        s["events"][1]["to"] = "study"
    elif name == "exploration_both":
        s["exploration"] = {"draws_per_player": 1, "rounds": [{"draws_per_player": 1}]}
    elif name == "exploration_neither":
        s["exploration"] = {}
    elif name == "exploration_rounds_empty":
        s["exploration"] = {"rounds": []}
    elif name == "exploration_round_unknown_field":
        s["exploration"] = {"rounds": [{"draws_per_player": 1}, {"draws": 1}]}
    return s


for name, doc, raw in SCHEMA:
    CASES.append(("schema", name, doc, ["input_error"], raw if raw is not None else schema_case(name)))


# ---------------------------------------------------------------- 仕様書 §9 の例
def spec_example():
    text = open(os.path.join(ROOT, "docs", "spec.md"), encoding="utf-8").read()
    sec = text[text.index("## 9. 例"):]
    inp = re.search(r"```jsonc\n(.*?)```", sec, re.S).group(1)
    exp = re.search(r"```json\n(.*?)```", sec, re.S).group(1)
    return json.loads(inp), json.loads(exp)


def write(path, content):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write(content)


def main():
    for group, name, doc, expect, scen in CASES:
        path = os.path.join(OUT, group, name + ".input.json")
        if isinstance(scen, str):
            write(path, scen)
            write(os.path.join(OUT, group, name + ".case.json"),
                  json.dumps({"doc": doc, "expect": expect}, ensure_ascii=False, indent=2) + "\n")
            continue
        scen = {"_case": {"doc": doc, "expect": expect}, **scen}
        write(path, json.dumps(scen, ensure_ascii=False, indent=2) + "\n")
    inp, exp = spec_example()
    write(os.path.join(OUT, "spec", "example.input.json"), json.dumps(inp, ensure_ascii=False, indent=2) + "\n")
    write(os.path.join(OUT, "spec", "example.spec_expected.json"), json.dumps(exp, ensure_ascii=False, indent=2) + "\n")
    print(f"{len(CASES) + 1} cases written to {os.path.relpath(OUT, ROOT)}")


if __name__ == "__main__":
    main()
