.PHONY: all lean cases oracle go test diff-check live-diff fuzz clean

ORACLE := lean/.lake/build/bin/oracle

all: lean go

# Lean: 仕様・証明のビルド(証明が通らなければ失敗する)
lean:
	cd lean && lake build

# テストケースの入力を作り直す(手書き: tools/oracle/cases.py、ランダム生成: tools/oracle/gen.py)
cases:
	python3 tools/oracle/cases.py
	python3 tools/oracle/gen.py

# Lean オラクルで期待出力(testdata/oracle/**/*.expected.json, examples/*/expected.json)を作り直し、点検する
oracle: lean
	python3 tools/oracle/regen.py $(ORACLE)
	python3 tools/oracle/check.py

go:
	cd go && go build -o ../bin/mmcheck ./cmd/mmcheck

# Go 側のテスト(ゴールデン差分テストを含む)
test:
	cd go && go vet ./... && go test ./...

# ライブ差分テスト: その場で作ったシナリオで Go と Lean オラクルの出力を比べる(N 件、SEED は省略可)
N ?= 500
live-diff: lean go
	python3 tools/oracle/live.py --oracle $(ORACLE) --mmcheck bin/mmcheck --count $(N) $(if $(SEED),--seed $(SEED))

# Go のファズテスト(パニックしない、出力が正規順序で重複なし)
FUZZTIME ?= 60s
fuzz:
	cd go && go test ./internal/check/ -run '^$$' -fuzz=FuzzCheck -fuzztime=$(FUZZTIME)

# 入力と期待出力を作り直しても、コミット済みのものと差分がないこと(CI 用)
diff-check: cases oracle
	@test -z "$$(git status --porcelain -- testdata/oracle examples)" || \
		(git status --porcelain -- testdata/oracle examples; echo "testdata/oracle or examples is out of date: run make cases oracle and commit"; exit 1)

clean:
	rm -rf bin lean/.lake/build
