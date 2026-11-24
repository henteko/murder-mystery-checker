// Package model は正規化 JSON (docs/spec.md §1) に対応するデータ型。
// Lean の lean/MurderMystery/Spec/Types.lean と1対1に対応する。
package model

// Character はキャラクター。
type Character struct {
	ID  string
	NPC bool
}

// Area はエリア。
type Area struct {
	ID              string
	InternalMinutes *int
}

// Location は場所。
type Location struct {
	ID     string
	Area   *string
	Public bool
}

// Edge は travel / area_travel / perception の1エントリ。perception では Minutes を使わない。
type Edge struct {
	Src, Dst      string
	Minutes       int
	Bidirectional bool
}

// Placement は初期配置。
type Placement struct {
	Character, Location string
}

// HolderKind はアイテムの保持者の種類。
type HolderKind int

const (
	HolderChar HolderKind = iota
	HolderPlace
	HolderConsumed
)

// Holder はアイテムの保持者 (§2.1)。
type Holder struct {
	Kind HolderKind
	ID   string
}

// Render は検出結果の args に使う表記。
func (h Holder) Render() string {
	switch h.Kind {
	case HolderChar:
		return "character:" + h.ID
	case HolderPlace:
		return "location:" + h.ID
	default:
		return "consumed"
	}
}

// Item はアイテム。
type Item struct {
	ID      string
	Initial Holder
	Tags    []string
}

// Fact は知識。
type Fact struct {
	ID             string
	Truth          bool
	ContradictedBy []string
	AboutEvent     *string
	AboutPoint     string
	ClaimedAt      *int
	Tolerance      *int
}

// Kind はイベントの種類。
type Kind int

const (
	Move Kind = iota
	Scene
	Observe
	Transfer
	Pickup
	Drop
	Use
	Consume
	Learn
	Tell
	Die
)

// EventKind はイベントの種類ごとのフィールド。使うフィールドは種類による:
//
//	move: Character To Arrive Mode Fatal / scene: Location Participants Reveals
//	observe: Character Location TargetLocation Targets Facts / transfer, tell: Src Dst (Item | Facts)
//	pickup, drop, use, consume: Character Item / learn: Character Facts / die: Character
type EventKind struct {
	Kind           Kind
	Character      string
	To             string
	Arrive         int
	Mode           string
	Fatal          bool
	Location       string
	Participants   []string
	Reveals        []string
	TargetLocation string
	Targets        []string
	Facts          []string
	Src, Dst       string
	Item           string
}

// Event はイベント。
type Event struct {
	ID       string
	Time     int
	Kind     EventKind
	Requires []string
}

// Clue は手がかり。
type Clue struct {
	ID       string
	Location *string
	Item     *string
	Deck     *string
	Reveals  []string
}

// AssertKind は断言の種類。
type AssertKind int

const (
	Present AssertKind = iota
	Absent
)

// Render は検出結果の args に使う表記。
func (k AssertKind) Render() string {
	if k == Present {
		return "present"
	}
	return "absent"
}

// Assertion は真相の断言。
type Assertion struct {
	ID         string
	Kind       AssertKind
	Location   string
	Time       int
	Characters []string
}

// Handout はハンドアウト。Items / Knows は省略(nil)と空の配列を区別する。
type Handout struct {
	Character string
	Location  *string
	Items     *[]string
	Knows     *[]string
}

// Board は盤面。
type Board struct {
	Location string
	Items    []string
}

// Goal はゴール。
type Goal struct {
	ID                string
	Owner             string
	RequiresItems     []string
	RequiresKnowledge []string
	// Condition は達成条件(ゴール ⇔ Condition)。nil なら条件なし
	Condition *Formula
	// RequiresTagged はタグ Tag のアイテムを Count 個以上持つこと(必要条件)
	RequiresTagged []TagReq
	// Conceals はほかのプレイヤーに知られてはいけない知識
	Conceals []string
}

// TagReq はタグのついたアイテムの個数の要求。
type TagReq struct {
	Tag   string
	Count int
}

// Choice はプレイヤーの選択。Values が nil なら真偽値の選択。
type Choice struct {
	ID     string
	Owner  string
	Values *[]string
}

// FormulaKind は論理式の種類。
type FormulaKind int

const (
	FConst FormulaKind = iota
	FVar
	FEq
	FPlurality
	FTie
	FNot
	FAnd
	FOr
	// FTruth は知識 Var が真か。Const に読み込み時の値を入れる(§1.9)
	FTruth
)

// Formula は論理式 (§1.9)。
type Formula struct {
	Kind  FormulaKind
	Const bool
	Var   string    // var / eq
	Value string    // eq / plurality
	Votes []string  // plurality / tie
	Subs  []Formula // not (1つ) / and / or
}

// Ending はエンディング。
type Ending struct {
	ID        string
	Condition Formula
}

// Pair は (character, fact) の組。
type Pair struct{ Character, Fact string }

// Scenario はシナリオ全体。
type Scenario struct {
	StartTime        int
	EndTime          int
	ClaimTolerance   int
	Characters       []Character
	Areas            []Area
	Locations        []Location
	Travel           []Edge
	AreaTravel       []Edge
	Perception       []Edge
	Placements       []Placement
	Items            []Item
	Facts            []Fact
	InitialKnowledge []Pair
	Events           []Event
	Clues            []Clue
	SolutionFacts    []string
	Assertions       []Assertion
	Handouts         []Handout
	Board            []Board
	Goals            []Goal
	Choices          []Choice
	Constraints      []Formula
	Endings          []Ending
	// Exploration は探索フェイズで1人が引ける枚数。nil なら探索の検査をしない
	Exploration *int
}
