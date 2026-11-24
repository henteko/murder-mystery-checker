"""ランダムに生成したオラクル用テストケースを testdata/oracle/gen/ に書き出す。

乱数の種は固定なので、何度実行しても同じファイルになる。
多くはおおむね正しいシナリオで、ところどころに誤り(移動時間不足、持っていない物、
存在しない参照、同時刻の重なりなど)を混ぜて、さまざまな規則が出るようにする。

使い方: python3 tools/oracle/gen.py [件数]
"""
import json
import os
import random
import sys

ROOT = os.path.normpath(os.path.join(os.path.dirname(__file__), "..", ".."))
OUT = os.path.join(ROOT, "testdata", "oracle", "gen")
SEED = 20261124


def gen(rng: random.Random, n: int):
    start = 600 + rng.randrange(0, 600)
    end = start + rng.randrange(30, 120)
    chars = [f"c{i}" for i in range(rng.randint(2, 4))]
    npcs = set(rng.sample(chars, k=rng.randint(0, 1)))
    areas = ["a0", "a1"][: rng.randint(1, 2)]
    locs = [f"l{i}" for i in range(rng.randint(2, 5))]
    loc_area = {l: rng.choice(areas + [None]) for l in locs}
    s = {
        "spec_version": "0.7.0",
        "_case": {"doc": f"ランダム生成 (seed {SEED}, #{n})"},
        "start_time": start, "end_time": end,
        "claim_tolerance": rng.choice([0, 0, 2, 5]),
        "characters": [{"id": c, **({"npc": True} if c in npcs else {})} for c in chars],
        "areas": [{"id": a, **({"internal_minutes": rng.randint(1, 6)} if rng.random() < 0.8 else {})} for a in areas],
        "locations": [{"id": l, **({"area": loc_area[l]} if loc_area[l] else {}),
                       **({"public": True} if rng.random() < 0.2 else {})} for l in locs],
    }
    # 移動時間・知覚の表
    pairs = [(a, b) for a in locs for b in locs if a < b]
    s["travel"] = [{"from": a, "to": b, "minutes": rng.randint(1, 8), "bidirectional": rng.random() < 0.7}
                   for a, b in rng.sample(pairs, k=min(len(pairs), rng.randint(0, 3)))]
    if len(areas) == 2 and rng.random() < 0.7:
        s["area_travel"] = [{"from": "a0", "to": "a1", "minutes": rng.randint(3, 10), "bidirectional": True}]
    s["perception"] = [{"from": a, "to": b, "bidirectional": rng.random() < 0.5}
                       for a, b in rng.sample(pairs, k=min(len(pairs), rng.randint(0, 2)))]
    if rng.random() < 0.05:  # R005
        s["travel"].append({"from": locs[0], "to": locs[0], "minutes": 1})
    s["placements"] = [{"character": c, "location": rng.choice(locs)} for c in chars]
    if rng.random() < 0.04:  # R003
        s["placements"].pop()
    # アイテム・知識
    items = [f"i{i}" for i in range(rng.randint(1, 3))]
    s["items"] = [{"id": i, "initial": ({"character": rng.choice(chars)} if rng.random() < 0.6
                                        else {"location": rng.choice(locs)})} for i in items]
    for it in s["items"]:  # タグ (0.7.0)
        if rng.random() < 0.5:
            it["tags"] = rng.sample(["ta", "tb"], k=rng.randint(1, 2))
    facts = [f"f{i}" for i in range(rng.randint(2, 5))]
    false_facts = set(rng.sample(facts, k=rng.randint(0, 1)))
    s["facts"] = []
    for f in facts:
        d = {"id": f}
        if f in false_facts:
            d["truth"] = False
            d["contradicted_by"] = rng.sample([x for x in facts if x not in false_facts], k=1)
        s["facts"].append(d)
    s["initial_knowledge"] = [{"character": rng.choice(chars), "fact": rng.choice(facts)}
                              for _ in range(rng.randint(0, 3))]
    # イベント: 状態をざっくり追いながら、おおむね正しいものを作る
    pos = {p["character"]: p["location"] for p in s["placements"]}
    busy_until = {c: start for c in chars}
    holder = {i["id"]: i["initial"] for i in s["items"]}
    events = []
    t = start
    for k in range(rng.randint(3, 12)):
        t += rng.choice([0, 1, 2, 3, 5, 8])
        if t >= end:
            break
        c = rng.choice(chars)
        kind = rng.choice(["move", "move", "scene", "learn", "tell", "observe", "transfer", "pickup",
                           "drop", "use", "consume", "die"])
        eid = f"e{k:02d}"
        e = {"id": eid, "at": t, "kind": kind}
        if kind == "move":
            to = rng.choice([l for l in locs if l != pos.get(c)] or locs)
            arr = t + rng.choice([0, 1, 3, 5, 8, 12])
            e.update(character=c, to=to, arrive=arr)
            if rng.random() < 0.1:
                e["mode"] = rng.choice(["fall", "carried"])
                e["fatal"] = rng.random() < 0.5
            pos[c], busy_until[c] = to, arr
        elif kind == "scene":
            here = [x for x in chars if pos.get(x) == pos.get(c)]
            e.update(location=pos.get(c, locs[0]), participants=sorted(set([c] + rng.sample(here, k=min(len(here), 2)))))
            if rng.random() < 0.5:
                e["reveals"] = [rng.choice(facts)]
        elif kind == "learn":
            e.update(character=c, facts=[rng.choice(facts)])
        elif kind == "tell":
            other = rng.choice([x for x in chars if x != c] or chars)
            e.update(**{"from": c, "to": other, "facts": [rng.choice(facts)]})
        elif kind == "observe":
            tl = rng.choice(locs)
            targets = [x for x in chars if x != c and rng.random() < 0.5]
            e.update(character=c, location=pos.get(c, locs[0]), target_location=tl, targets=targets,
                     facts=[rng.choice(facts)])
        elif kind in ("transfer", "pickup", "drop", "use", "consume"):
            i = rng.choice(items)
            if kind == "transfer":
                other = rng.choice([x for x in chars if x != c] or chars)
                e.update(**{"from": c, "to": other, "item": i})
                holder[i] = {"character": other}
            else:
                e.update(character=c, item=i)
                if kind == "pickup":
                    holder[i] = {"character": c}
                elif kind == "drop":
                    holder[i] = {"location": pos.get(c, locs[0])}
                elif kind == "consume":
                    holder[i] = None
        elif kind == "die":
            e.update(character=c)
        if rng.random() < 0.15:
            e["requires"] = [rng.choice(facts)]
        events.append(e)
    if events and rng.random() < 0.04:  # R002
        e = rng.choice(events)
        e["character" if "character" in e else "to"] = "ghost"
    rng.shuffle(events)  # 入力の順番は意味を持たない
    s["events"] = events
    # 証言
    if events and rng.random() < 0.5:
        e = rng.choice(events)
        point = "arrive" if e["kind"] == "move" and rng.random() < 0.5 else "at"
        actual = e["arrive"] if point == "arrive" else e["at"]
        s["facts"].append({"id": "f_claim", "about": {"event": e["id"], "point": point},
                           "claimed_at": actual + rng.choice([0, 0, 1, 3, 10])})
    # 手がかり・真相・断言
    s["clues"] = []
    for k in range(rng.randint(0, 4)):
        cl = {"id": f"cl{k}", "reveals": rng.sample(facts, k=rng.randint(1, min(2, len(facts))))}
        r = rng.random()
        if r < 0.4:
            cl["location"] = rng.choice(locs)
        elif r < 0.7:
            cl["item"] = rng.choice(items)
            if rng.random() < 0.5:
                cl["location"] = rng.choice(locs)
        else:
            cl["deck"] = "deck"
        s["clues"].append(cl)
    s["solution_facts"] = rng.sample(facts, k=rng.randint(0, 2))
    s["assertions"] = [{"id": f"as{k}", "kind": rng.choice(["present", "absent"]), "location": rng.choice(locs),
                        "at": rng.randrange(start, end), "characters": [rng.choice(chars)]}
                       for k in range(rng.randint(0, 2))]
    # ハンドアウト・盤面(終了状態をおおむね反映し、ときどき外す)
    s["handouts"] = []
    for c in rng.sample(chars, k=rng.randint(0, len(chars))):
        h = {"character": c}
        if rng.random() < 0.6:
            h["location"] = pos.get(c) if rng.random() < 0.8 else rng.choice(locs)
        if rng.random() < 0.5:
            h["items"] = [i for i, hd in holder.items() if hd == {"character": c}]
        if rng.random() < 0.4:
            h["knows"] = rng.sample(facts, k=rng.randint(0, 2))
        s["handouts"].append(h)
    s["board"] = []
    for l in rng.sample(locs, k=rng.randint(0, 2)):
        s["board"].append({"location": l, "items": [i for i, hd in holder.items() if hd == {"location": l}]})
    # ゴール・選択・エンディング
    pcs = [c for c in chars if c not in npcs]
    s["goals"] = []
    for k, c in enumerate(pcs):
        if rng.random() < 0.85:
            g = {"id": f"g{k}", "owner": c}
            if rng.random() < 0.3:
                g["requires_items"] = [rng.choice(items)]
            s["goals"].append(g)
    nvote = rng.randint(1, 3)
    values = ["p", "q", "r"][: rng.randint(2, 3)]
    s["choices"] = [{"id": f"v{k}", "owner": rng.choice(pcs or chars), "values": values} for k in range(nvote)]
    if rng.random() < 0.3:
        s["choices"].append({"id": "flag", "owner": rng.choice(pcs or chars)})
    votes = [ch["id"] for ch in s["choices"] if "values" in ch]
    # ゴールの必要な知識と達成条件 (0.6.0)、タグ・隠す知識 (0.7.0)
    for g in s["goals"]:
        if rng.random() < 0.3:
            g["requires_tagged"] = [{"tag": rng.choice(["ta", "tb"]), "count": rng.randint(1, 2)}
                                    for _ in range(rng.randint(1, 2))]
        if facts and rng.random() < 0.25:
            g["conceals"] = rng.sample(facts, k=1)
        if facts and rng.random() < 0.25:
            g["requires_knowledge"] = rng.sample(facts, k=rng.randint(1, min(2, len(facts))))
        if rng.random() < 0.3:
            opts = [{"eq": {"var": votes[0], "value": rng.choice(values)}},
                    {"not": {"eq": {"var": votes[-1], "value": rng.choice(values)}}},
                    {"plurality": {"votes": votes, "value": rng.choice(values)}},
                    {"const": rng.random() < 0.5},
                    {"truth": rng.choice(facts)},
                    {"or": [{"and": [{"truth": rng.choice(facts)}, {"eq": {"var": votes[0], "value": rng.choice(values)}}]},
                            {"not": {"truth": rng.choice(facts)}}]}]
            others = [h["id"] for h in s["goals"] if h is not g]
            if others:
                opts.append({"var": rng.choice(others)})
            if any(ch["id"] == "flag" for ch in s["choices"]):
                opts.append({"var": "flag"})
            if rng.random() < 0.05:  # R009 / R002
                opts = [{"var": votes[0]}, {"var": "no_such_var"}]
            g["condition"] = rng.choice(opts)
    style = rng.random()
    if style < 0.4:
        s["endings"] = [{"id": f"end_{v}", "condition": {"plurality": {"votes": votes, "value": v}}} for v in values]
        s["endings"].append({"id": "end_tie", "condition": {"tie": {"votes": votes}}})
    elif style < 0.7:
        s["endings"] = [{"id": f"end_{v}", "condition": {"eq": {"var": votes[0], "value": v}}} for v in values]
    else:
        g = s["goals"][0]["id"] if s["goals"] else None
        win = {"var": g} if g else {"const": True}
        s["endings"] = [{"id": "end_win", "condition": {"and": [win, {"eq": {"var": votes[0], "value": values[0]}}]}},
                        {"id": "end_lose", "condition": {"not": win}}]
    if rng.random() < 0.3 and s["endings"]:
        s["endings"].pop(rng.randrange(len(s["endings"])))
    if rng.random() < 0.5:  # 探索フェイズ (0.7.0)
        s["exploration"] = {"draws_per_player": rng.randint(0, 2)}
    s["constraints"] = []
    if rng.random() < 0.3 and s["goals"]:
        s["constraints"].append(rng.choice([{"var": s["goals"][0]["id"]},
                                            {"not": {"var": s["goals"][0]["id"]}},
                                            {"or": [{"var": g["id"]} for g in s["goals"]]}]))
    if rng.random() < 0.03:  # R001
        s["characters"].append({"id": chars[0]})
    return s


def main():
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    rng = random.Random(SEED)
    os.makedirs(OUT, exist_ok=True)
    for old in os.listdir(OUT):
        if old.endswith(".input.json"):
            os.remove(os.path.join(OUT, old))
    for n in range(count):
        s = gen(rng, n)
        with open(os.path.join(OUT, f"gen_{n:03d}.input.json"), "w", encoding="utf-8") as f:
            f.write(json.dumps(s, ensure_ascii=False, indent=1) + "\n")
    print(f"{count} generated cases written to {os.path.relpath(OUT, ROOT)}")


if __name__ == "__main__":
    main()
