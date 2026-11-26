"""シナリオをランダムに少し変える(差分テスト用)。

どの変異も「作者がやりがちな書き間違い」に近いものにして、規則の境界を通るようにする。
"""
import copy
import json

from gen import random_exploration


def _events(s):
    return s.setdefault("events", [])


def _chars(s):
    return [c["id"] for c in s.get("characters", []) if isinstance(c, dict) and "id" in c] or ["ghost"]


def _locs(s):
    return [l["id"] for l in s.get("locations", []) if isinstance(l, dict) and "id" in l] or ["nowhere"]


def mutate(rng, s, steps=None):
    s = copy.deepcopy(s)
    for _ in range(steps or rng.randint(1, 4)):
        op = rng.randrange(18)
        evs = _events(s)
        if op == 0 and evs:  # 時刻をずらす
            e = rng.choice(evs)
            d = rng.randint(-20, 20)
            e["at"] = max(0, e["at"] + d)
            if e.get("kind") == "move":
                e["arrive"] = max(0, e.get("arrive", e["at"]) + d + rng.randint(-3, 3))
        elif op == 1 and evs:  # イベントを消す
            evs.pop(rng.randrange(len(evs)))
        elif op == 2 and evs:  # 行き先を変える
            mv = [e for e in evs if e.get("kind") == "move"]
            if mv:
                rng.choice(mv)["to"] = rng.choice(_locs(s))
        elif op == 3 and evs:  # 行為者を変える
            xs = [e for e in evs if "character" in e]
            if xs:
                rng.choice(xs)["character"] = rng.choice(_chars(s))
        elif op == 4 and s.get("facts"):  # 真偽を反転
            f = rng.choice(s["facts"])
            f["truth"] = not f.get("truth", True)
            if f["truth"]:
                f.pop("contradicted_by", None)
        elif op == 5 and s.get("clues"):
            s["clues"].pop(rng.randrange(len(s["clues"])))
        elif op == 6 and s.get("endings"):
            s["endings"].pop(rng.randrange(len(s["endings"])))
        elif op == 7 and s.get("handouts"):  # ハンドアウトの記述を減らす
            h = rng.choice(s["handouts"])
            for k in ("knows", "items"):
                if h.get(k):
                    h[k].pop(rng.randrange(len(h[k])))
        elif op == 8 and s.get("assertions"):
            a = rng.choice(s["assertions"])
            a["at"] = max(0, a["at"] + rng.randint(-15, 15))
        elif op == 9:  # 要素を複製する(ID の重複)
            keys = [k for k in ("characters", "facts", "events", "items", "choices", "endings", "locations")
                    if s.get(k)]
            if keys:
                k = rng.choice(keys)
                s[k].append(copy.deepcopy(rng.choice(s[k])))
        elif op == 10 and evs:  # 同時刻に観察と出発(T012)
            chars = _chars(s)
            if len(chars) >= 2:
                a, b = rng.sample(chars, 2)
                t = rng.choice(evs)["at"]
                loc = rng.choice(_locs(s))
                evs.append({"id": f"zz_obs{rng.randrange(1000)}", "at": t, "kind": "observe", "character": a,
                            "location": loc, "targets": [b], "facts": [rng.choice(s.get("facts") or [{"id": "f"}])["id"]]})
                evs.append({"id": f"aa_mv{rng.randrange(1000)}", "at": t, "kind": "move", "character": b,
                            "to": rng.choice(_locs(s)), "arrive": t + rng.randint(0, 5)})
        elif op == 11 and s.get("items"):  # 初期の保持者を変える
            it = rng.choice(s["items"])
            it["initial"] = rng.choice([{"character": rng.choice(_chars(s))}, {"location": rng.choice(_locs(s))}])
        elif op == 12 and s.get("goals"):  # ゴールに必要なアイテム
            items = [i["id"] for i in s.get("items", [])]
            if items:
                rng.choice(s["goals"])["requires_items"] = [rng.choice(items)]
        elif op == 13 and s.get("choices"):  # 選択の値を変える
            c = rng.choice(s["choices"])
            if c.get("values") and rng.random() < 0.5:
                c["values"] = c["values"][:-1] or ["x"]
            else:
                c.pop("values", None)
        elif op == 14:  # 制約を足す
            vars_ = [g["id"] for g in s.get("goals", [])] + [c["id"] for c in s.get("choices", []) if "values" not in c]
            if vars_:
                v = rng.choice(vars_)
                s.setdefault("constraints", []).append(rng.choice([{"var": v}, {"not": {"var": v}}]))
        elif op == 15 and evs:  # 死亡を足す
            evs.append({"id": f"zz_die{rng.randrange(1000)}", "at": rng.choice(evs)["at"], "kind": "die",
                        "character": rng.choice(_chars(s))})
        elif op == 16:  # 探索を回に分ける
            s["exploration"] = random_exploration(rng, s)
        elif op == 17:  # 探索を 1 回に戻す、またはなくす
            if rng.random() < 0.5:
                s["exploration"] = {"draws_per_player": rng.randint(0, 3)}
            else:
                s.pop("exploration", None)
    return s


def shuffle_arrays(rng, s):
    """トップレベルの配列をそれぞれ並べ替える(出力は変わらないはず: 定理 3)。"""
    s = copy.deepcopy(s)
    for v in s.values():
        if isinstance(v, list):
            rng.shuffle(v)
    return s


def corrupt(rng, s):
    """入力エラーになりうる形に壊す(壊れていない場合もある)。結果は JSON の文字列。"""
    s = copy.deepcopy(s)
    op = rng.randrange(10)
    if op == 0:
        k = rng.choice(["characters", "locations", "placements", "start_time", "end_time"])
        s.pop(k, None)
    elif op == 1 and s.get("events"):
        rng.choice(s["events"])["at"] = rng.choice(["1260", -1, 1260.5, 10000001, True, None, 1260.0])
    elif op == 2 and s.get("events"):
        rng.choice(s["events"])["kind"] = rng.choice(["teleport", "", 3])
    elif op == 3 and s.get("characters"):
        rng.choice(s["characters"])["id"] = rng.choice(["", 1, None])
    elif op == 4 and s.get("endings"):
        rng.choice(s["endings"])["condition"] = rng.choice([{}, {"var": "x", "const": True}, [], {"const": None}])
    elif op == 5 and s.get("items"):
        rng.choice(s["items"])["initial"] = rng.choice([{}, {"character": "a", "location": "b"}, "x"])
    elif op == 8:  # 知らないキー(note と _ で始まるキー、説明の name / text は読み飛ばす)
        targets = [s] + [x for k in ("characters", "events", "clues", "facts", "goals", "items", "locations")
                         for x in s.get(k, []) if isinstance(x, dict)]
        if isinstance(s.get("exploration"), dict):
            targets.append(s["exploration"])
            targets += [r for r in s["exploration"].get("rounds", []) if isinstance(r, dict)]
        k = rng.choice(["phases", "foo", "note", "_meta", "name", "text", "draws", "rounds", "to", "facts"])
        rng.choice(targets)[k] = rng.choice(["x", 1, [], {"a": 1}])
    elif op == 9:  # 探索の形を壊す
        s["exploration"] = rng.choice([
            {}, {"draws_per_player": 1, "rounds": [{"draws_per_player": 1}]}, {"rounds": []},
            {"rounds": [{}]}, {"rounds": [{"draws_per_player": 1, "clues": "c0"}]}, {"rounds": "x"},
            {"rounds": [{"draws_per_player": 1, "clues": None}]}, {"rounds": [{"draws_per_player": -1}]}])
    text = json.dumps(s, ensure_ascii=False)
    if op == 6:  # 末尾を切る
        text = text[: rng.randrange(1, len(text))]
    elif op == 7:  # キーを重複させる
        text = text.replace('"start_time"', '"start_time": 0, "start_time"', 1)
    return text
