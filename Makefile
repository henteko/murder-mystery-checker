.PHONY: all lean oracle go test diff-check clean

all: lean go

# Lean: 仕様・証明のビルド(証明が通らなければ失敗する)
lean:
	cd lean && lake build

# Lean オラクルで testdata/oracle/*.expected.json を再生成する(Phase 3 で実装)
oracle: lean
	@echo "TODO(Phase 3): generate testdata/oracle from Lean oracle"

go:
	cd go && go build -o ../bin/mmcheck ./cmd/mmcheck

# Go 側のテスト(ゴールデン差分テストを含む)
test:
	cd go && go vet ./... && go test ./...

# オラクル再生成後にコミット済みのゴールデンとの差分がないこと(CI 用)
diff-check: oracle
	git diff --exit-code -- testdata/oracle

clean:
	rm -rf bin lean/.lake/build
