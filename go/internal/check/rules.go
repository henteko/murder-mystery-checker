package check

import (
	"sort"
	"strconv"
)

// Rule は規則1つの説明(AI やツールに渡すためのもの)。判定には使わない。
// Args は検出結果の args の各位置の名前(docs/spec.md §4 の args 列と同じ数・順)。
// Hint は直し方の短いヒント。
type Rule struct {
	Code     string   `json:"code"`
	Severity string   `json:"severity"`
	Message  string   `json:"message"`
	Args     []string `json:"args"`
	Hint     string   `json:"hint"`
}

var argNames = map[string][]string{
	"R001": {"kind", "id"}, "R002": {"referrer", "kind", "id"}, "R003": {"character"}, "R004": {},
	"R005": {"table", "from", "to"}, "R006": {"reason"}, "R007": {"clue"}, "R008": {"choice"},
	"R009": {"referrer", "variable", "value"}, "R010": {"fact", "refuter"}, "R011": {"fact", "reason"},
	"R012": {"referrer", "reason"}, "R013": {"assertion"},
	"T001": {}, "T002": {"character", "from", "to"}, "T003": {"character", "from", "to", "minutes"},
	"T004": {"character", "location"}, "T005": {"character", "other_event"}, "T006": {"character", "moving_to"},
	"T007": {"character", "required_location", "actual_location"},
	"T008": {"from", "to", "from_location", "to_location"},
	"T009": {"character1", "character2", "location", "from_time", "to_time"},
	"T010": {"character", "death_time"}, "T011": {"character", "location", "target_location"},
	"T012": {"target", "move_event"},
	"I001": {"holder", "item", "actual_holder"}, "I002": {"actor", "item"},
	"I003": {"character", "item", "actual_holder"}, "I004": {"item", "other_event"},
	"K001": {"from", "fact"}, "K002": {"actor", "fact"}, "K003": {"fact"}, "K004": {"clue", "item"},
	"K005": {"clue", "item", "location", "actual_holder"}, "K006": {"fact"}, "K007": {"fact"},
	"K008": {"fact", "claimed_at", "actual"}, "K009": {"cards", "draws"}, "K010": {"draws"},
	"H001": {"character", "handout_location", "actual_location"}, "H002": {"character", "item", "actual_holder"},
	"H003": {"character", "item"}, "H004": {"character", "fact"}, "H005": {"character", "fact"},
	"H006": {"location", "item", "actual_holder"}, "H007": {"location", "item"},
	"A001": {"assertion", "character", "kind", "actual_location"},
	"G001": {}, "G002": {"ending1", "ending2"}, "G003": {"ending"}, "G004": {"goal"}, "G005": {},
	"G006": {"variable"}, "G007": {"assignments"}, "G008": {"character"}, "G009": {"choice", "value"},
}

// timeArgs は値が時刻(分)の引数。
var timeArgs = map[string]bool{"from_time": true, "to_time": true, "death_time": true, "claimed_at": true, "actual": true}

var hints = map[string]string{
	"R001": "ID を一意にする(goal と choice は同じ名前空間)",
	"R002": "参照先の ID を定義するか、参照を正しい ID に直す",
	"R003": "そのキャラクターの初期配置(placements)をちょうど1つ書く",
	"R004": "start_time を end_time 以下にする",
	"R005": "移動時間・知覚の表から、同じ場所どうしのエントリや重複を消す",
	"R006": "reason に従ってイベントを直す(move の arrive は at 以上、scene の参加者は2人以上、など)",
	"R007": "手がかりに location・item・deck のどれかを書く",
	"R008": "選択肢の values を空でなく重複のないリストにする",
	"R009": "var は真偽値の変数(ゴール・真偽値の選択)に、eq は列挙型の選択とその values の値に使う",
	"R010": "truth: true の知識から contradicted_by を外す。contradicted_by には真の知識だけを書く",
	"R011": "証言は about と claimed_at を両方書き、point は at か arrive にする(arrive は move のみ)",
	"R012": "集計の votes には、同じ値の集合を持つ列挙型の選択を1つ以上並べる",
	"R013": "断言の at を start_time 以上、end_time 未満にする",
	"T001": "イベントの時刻をシナリオの時間内にする",
	"T002": "移動元と移動先の間に移動時間を定義する(travel / エリアの internal_minutes / area_travel)",
	"T003": "到着(arrive)を遅らせるか、出発を早める。必要な分数は args の minutes",
	"T004": "移動先を今いる場所と別にするか、move を消す",
	"T005": "片方のイベントの時刻をずらす(同じ人は同じ時刻に1つのイベントだけ)",
	"T006": "到着後にイベントを置くか、移動の到着を早める",
	"T007": "対象者をその時刻にその場所へ移動させるか、場所を対象者のいる場所に直す",
	"T008": "2人を同じ場所に集めてから渡す・話す",
	"T009": "2人が気づいた記述(scene や observe)を足すか、居合わせないよう時刻をずらす(警告)",
	"T010": "死亡より前にイベントを移すか、そのイベントを消す",
	"T011": "perception にその場所から見える場所を足すか、観察する場所を変える",
	"T012": "観察か移動の時刻を1分ずらす(同じ時刻だと処理順で結果が変わる)(警告)",
	"I001": "先にそのアイテムを手に入れるイベント(pickup / transfer)を置く",
	"I002": "使い切った(consume)あとでそのアイテムを扱わない",
	"I003": "アイテムをその場所に置いてから拾う(initial か drop)",
	"I004": "同じアイテムを扱うイベントの時刻をずらす",
	"K001": "話す前に、その知識を知るイベント(learn / scene / observe / tell)を置く",
	"K002": "行動の前に、requires の知識を知るイベントを置く",
	"K003": "その知識を、手がかり(clues の reveals)かプレイヤーが知るイベントで手に入るようにする",
	"K004": "手がかりのアイテムを使い切らないようにする",
	"K005": "手がかりのアイテムを書いた場所に置く(drop など)か、手がかりの location を直す",
	"K006": "偽の知識の contradicted_by の知識を、プレイヤーが手に入れられるようにする",
	"K007": "solution_facts から偽の知識を外す",
	"K008": "証言の claimed_at を実際の時刻(args の actual)に合わせるか、tolerance を広げる",
	"K009": "探索カードを減らすか、draws_per_player を増やす(警告)",
	"K010": "真相の知識をまとめて明かす手がかりにするか、draws_per_player を増やす",
	"H001": "ハンドアウトの location を終了時の居場所に直す",
	"H002": "ハンドアウトの items を終了時の持ち物に直す",
	"H003": "ハンドアウトの items に持ち物を足す(警告)",
	"H004": "ハンドアウトの knows から知りえない知識を外すか、知るイベントを足す",
	"H005": "ハンドアウトの knows に知識を足す(警告)",
	"H006": "盤面の items をゲーム開始時の配置に合わせるか、アイテムをその場所に置く",
	"H007": "盤面の items にその場所のアイテムを足す(警告)",
	"A001": "断言の時刻・場所か、タイムラインのどちらかを直す",
	"G001": "witness の選び方で成り立つエンディングを足すか、条件を広げる",
	"G002": "2つのエンディングの条件が同時に成り立たないようにする",
	"G003": "そのエンディングの条件を、どれかの選び方で成り立つようにするか、エンディングを消す",
	"G004": "ゴールの condition・requires_items・requires_knowledge・conceals・requires_tagged を見直す",
	"G005": "constraints や導出制約(ゴールの条件)の矛盾を解く",
	"G006": "常に同じ値になるゴール・選択の条件を見直す(警告)",
	"G007": "変数(ゴールと選択)を減らすか、選択の values を減らす",
	"G008": "そのプレイヤーにゴールを1つ以上与える(警告)",
	"G009": "その値が選ばれうるよう制約を見直すか、values から外す(警告)",
}

var warningRules = map[string]bool{"T009": true, "T012": true, "K009": true, "H003": true, "H005": true,
	"H007": true, "G006": true, "G008": true, "G009": true}

// Rules は全規則の説明を、コード順に返す。
func Rules() []Rule {
	var out []Rule
	for c := range messages {
		sev := "error"
		if warningRules[c] {
			sev = "warning"
		}
		out = append(out, Rule{Code: c, Severity: sev, Message: messages[c], Args: argNames[c], Hint: hints[c]})
	}
	sort.Slice(out, func(i, j int) bool { return out[i].Code < out[j].Code })
	return out
}

// Hint は規則 code の直し方のヒント。
func Hint(code string) string { return hints[code] }

// NamedArg は名前つきの引数。Time は値が時刻(分)のとき、その「時:分」表記。
type NamedArg struct {
	Name  string `json:"name"`
	Value string `json:"value"`
	Time  string `json:"time,omitempty"`
}

// NameArgs は検出結果の args に名前を付ける(名前がなければ arg1, arg2, ...)。
func NameArgs(d Diag) []NamedArg {
	names := argNames[d.Code]
	out := make([]NamedArg, len(d.Args))
	for i, a := range d.Args {
		n := ""
		if i < len(names) {
			n = names[i]
		} else {
			n = "arg" + strconv.Itoa(i+1)
		}
		out[i] = NamedArg{Name: n, Value: a}
		if timeArgs[n] {
			if t, err := strconv.Atoi(a); err == nil {
				out[i].Time = FormatTime(t)
			}
		}
	}
	return out
}
