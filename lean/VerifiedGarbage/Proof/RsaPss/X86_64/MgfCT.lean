import VerifiedGarbage.Proof.RsaPss.X86_64.CtHashCT
import VerifiedGarbage.Proof.RsaPss.X86_64.Mgf

/-!
# RSASSA-PSS on x86-64: MGF1 is constant time

Two runs of `mgfXor` with the same frame, working space, writable regions
and place and length of `DB` (`MA`) leak the same trace (`mgfXor_ct`): the
loop runs once per `hLen` bytes of `DB` in both, each round's pieces between
the calls are checked by the taint analysis (`HashChecks`), and the hash is
constant time (`ctHash_ct`).
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum.X86_64 (off Two two_post two_map two_mono two_loop)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

/-- What two runs of `mgfXor` share: the frame, the working space, the
writable regions after the frame, and `DB`'s offset and length. -/
structure MA where
  F : Addr
  S : Addr
  rest : List Region
  e : Nat
  db : Nat

/-- The public words in round `j`: `scratch`, `DB`, `dbLen`, the counter and
the bytes done. -/
def mws (D : Nat) (a : MA) (j : Nat) : List (Nat × BitVec 64) :=
  [(21, a.S), (23, off a.S a.e), (24, BitVec.ofNat 64 a.db), (31, BitVec.ofNat 64 j),
    (32, BitVec.ofNat 64 (j * D))]

theorem mws_keys {D : Nat} {a : MA} {j : Nat} {q : Nat × BitVec 64} (hq : q ∈ mws D a j) :
    q.1 = 21 ∨ q.1 = 23 ∨ q.1 = 24 ∨ q.1 = 31 ∨ q.1 = 32 := by
  simp only [mws, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp

theorem mws_of {D : Nat} {a : MA} {j : Nat} {W : Nat → BitVec 64} (h21 : W 21 = a.S) (h23 : W 23 = off a.S a.e)
    (h24 : W 24 = BitVec.ofNat 64 a.db) (h31 : W 31 = BitVec.ofNat 64 j) (h32 : W 32 = BitVec.ofNat 64 (j * D)) :
    ∀ q ∈ mws D a j, W q.1 = q.2 := by
  intro q hq
  simp only [mws, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- The rounds of `dbLen` bytes, `hLen` at a time. -/
def mN (D : Nat) (a : MA) : Nat := (a.db + D - 1) / D

theorem cnt_iff {j D db : Nat} (hD : 0 < D) : j < (db + D - 1) / D ↔ j * D < db := by
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hD, Nat.succ_mul]
  omega

variable {H : Hash} (hH : HashOK H) (K : Callees H) (n : Nat)
variable {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x) (hGl : G.len = H.D) (hG : Proof.Mgf1.Valid G)

/-- The anchor fits `mgfXor`. -/
def MOk (a : MA) : Prop := RestOk n a.F a.rest ∧ DbAt H.D a.e a.db

variable (H) in
/-- At the start. -/
def ME (a : MA) (t : State) : Prop :=
  MOk (H := H) n a ∧
    Pub a.F a.S a.rest [(21, a.S), (23, off a.S a.e), (24, BitVec.ofNat 64 a.db)] [] (fun _ _ => True) t

variable (H G) in
/-- Before round `j`: the correctness proof's invariant. -/
def MI (a : MA) (j : Nat) (t : State) : Prop :=
  MOk (H := H) n a ∧ j * H.D < a.db ∧ ∃ (u₀ : State) (V : Nat → Byte) (W : Nat → BitVec 64),
    u₀.wr = ⟨a.F, frameBytes⟩ :: a.rest ∧ W 21 = a.S ∧ W 23 = off a.S a.e ∧ W 24 = BitVec.ofNat 64 a.db ∧
    MgfI u₀ a.F a.S V W (Spec.Mgf1.mgf1 G ((List.range H.D).map fun i => V (a.e + a.db + i)) a.db)
      a.e a.db H.D j t

/-- The words of round `j`, from the invariant. -/
theorem mi_rep {a : MA} {j : Nat} {t : State} (h : MI H n G a j t) :
    ∃ V W, Rep t.mem a.F a.S V W ∧ ∀ q ∈ mws H.D a j, W q.1 = q.2 := by
  obtain ⟨-, -, u₀, V, W, -, h21, h23, h24, I⟩ := h
  obtain ⟨V', W', R', h31, h32, hW, -⟩ := I.rep
  exact ⟨V', W', R', mws_of ((hW 21 (by decide) (.inl (by decide))).trans h21)
    ((hW 23 (by decide) (.inl (by decide))).trans h23) ((hW 24 (by decide) (.inl (by decide))).trans h24) h31 h32⟩

theorem mi_pub {a : MA} {j : Nat} {t : State} (h : MI H n G a j t) :
    Pub a.F a.S a.rest (mws H.D a j) [] (fun _ _ => True) t := by
  obtain ⟨V, W, R, hw⟩ := mi_rep n h
  obtain ⟨-, -, u₀, _, _, hwr, -, -, -, I⟩ := h
  exact ⟨I.L, I.wr.trans hwr, ⟨V, W, R, hw, trivial⟩, fun _ hp => by cases hp⟩

/-! ## Before the loop -/

include hH in
theorem mgfInit_ct (hfx : FixedChecks n) :
    RelCT isa (Two (ME H n)) (.block [.mov32 .rax (.imm 0), .store (sp sCtr) .rax, .store (sp sDone) .rax])
      (Two fun a t => 0 < mN H.D a ∧ MI H n G a 0 t) := by
  obtain ⟨_, hp⟩ := hfx.mgfInit
  refine two_post (two_pub n [21, 23, 24] [] MA.F MA.S MA.rest
    (fun a => [(21, a.S), (23, off a.S a.e), (24, BitVec.ofNat 64 a.db)]) (fun _ => []) (fun a t h => ⟨_, h.2⟩)
    (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_
  obtain ⟨V, W, R, hw, -⟩ := h.2.W
  have L := h.2.L
  have hD := hH.hD0
  have hdb1 := h.1.2.db1
  have G' := L.geo
  have R2 := (R.wf G' (k := 31) (by decide) 0#64).wf G' (k := 32) (by decide) 0#64
  rw [show off a.F (8 * 31) = off a.F sCtr from rfl, show off a.F (8 * 32) = off a.F sDone from rfl] at R2
  refine WP.mono (WP.keep [.rax] (Q := fun v => v.mem =
      (t.mem.writeW (off a.F sCtr) 0#64).writeW (off a.F sDone) 0#64) ?_ rfl) fun v ⟨hm, hk⟩ => ?_
  · xrun [ea_sp, L.rsp, L.st (d := sCtr) (by decide), L.st (d := sDone) (by decide),
      show BitVec.setWidth 64 (0 : BitVec 32) = 0#64 from rfl]
  have R2' : Rep v.mem a.F a.S V (upd (upd W 31 0#64) 32 0#64) := hm ▸ R2
  have Lv : Lay v a.F a.S := L.congr (hk.gpr (by decide)) hk.2.2 (by
    rw [slot_eq sScr 21 rfl, slot_eq sScr 21 rfl, R2'.fr 21 (by decide), R.fr 21 (by decide)]; simp [upd])
  refine ⟨(cnt_iff hD).mpr (by rw [Nat.zero_mul]; omega), h.1, by rw [Nat.zero_mul]; omega, t, V, W, h.2.wr,
    hw (21, a.S) (by simp), hw (23, off a.S a.e) (by simp), hw (24, BitVec.ofNat 64 a.db) (by simp),
    Lv, hk.2.1, hk.2.2, keep_cs hk (by decide), _, _, R2', by simp [upd], by simp [upd],
    fun k _ h => by simp only [upd, ifn (show k ≠ 32 by omega), ifn (show k ≠ 31 by omega)],
    fun o _ _ => by simp only [mixV, Nat.zero_mul, Nat.zero_min, Nat.add_zero]; rw [ifn (by omega)]⟩

/-! ## A round -/

variable (H G) in
/-- Round `j`, as the loop sees it. -/
abbrev MB (p : MA × Nat) (t : State) : Prop := p.2 < mN H.D p.1 ∧ MI H n G p.1 p.2 t

variable (H) in
/-- After `H` is copied to `Y`, cleared after it, and `rcx` is `Y`. -/
def M1 (p : MA × Nat) (t : State) : Prop :=
  MOk (H := H) n p.1 ∧ p.2 * H.D < p.1.db ∧ Pub p.1.F p.1.S p.1.rest (mws H.D p.1 p.2) [(.rcx, off p.1.S oY)]
    (fun V _ => ∀ i, H.D ≤ i → i < mgfNb H * H.P.B → V (oY + i) = 0) t

variable (H) in
/-- After the counter: `H ‖ C` in `Y`, cleared after it. -/
def M2 (p : MA × Nat) (t : State) : Prop :=
  MOk (H := H) n p.1 ∧ p.2 * H.D < p.1.db ∧
    Pub p.1.F p.1.S p.1.rest (mws H.D p.1 p.2 ++ [(28, BitVec.ofNat 64 (mgfNb H))]) []
      (fun V W => W 27 = BitVec.ofNat 64 (H.D + 4) ∧ ∀ i, H.D + 4 ≤ i → i < mgfNb H * H.P.B → V (oY + i) = 0) t

variable (H) in
/-- After the hash. -/
def M3 (p : MA × Nat) (t : State) : Prop :=
  MOk (H := H) n p.1 ∧ p.2 * H.D < p.1.db ∧ Pub p.1.F p.1.S p.1.rest (mws H.D p.1 p.2) [] (fun _ _ => True) t

variable (H) in
/-- After the digest is XORed into `DB`. -/
def M4 (p : MA × Nat) (t : State) : Prop :=
  MOk (H := H) n p.1 ∧ Pub p.1.F p.1.S p.1.rest (mws H.D p.1 p.2) [] (fun _ _ => True) t

theorem sub_mws {D : Nat} {a : MA} {j : Nat} {ws : List (Nat × BitVec 64)} (h : ∀ q ∈ ws, q ∈ mws D a j) :
    ∀ q ∈ ws, q ∈ mws D a j := h

include hH in
theorem clearCopy_ct (hc : HashChecks H.P H.D n) :
    RelCT isa (Two (MB H n G)) (.seq (clearBlock H) (copyH H)) (Two (M1 H n)) := by
  obtain ⟨_, hp⟩ := hc.clearCopyH
  refine two_post (two_pub n [21, 23, 24] [] (fun p => p.1.F) (fun p => p.1.S) (fun p => p.1.rest)
    (fun p => [(21, p.1.S), (23, off p.1.S p.1.e), (24, BitVec.ofNat 64 p.1.db)]) (fun _ => [])
    (fun p t h => ⟨_, (mi_pub n h.2).sub (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp [mws]) (fun _ h => h) fun _ _ x => x⟩)
    (fun p t h => h.2.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun p t h => ?_
  obtain ⟨V1, W1, R1, hw⟩ := mi_rep n h.2
  obtain ⟨hm, hj, u₀, _, _, hwr, -, -, -, I⟩ := h.2
  have w23 : W1 23 = off p.1.S p.1.e := hw (23, off p.1.S p.1.e) (by simp [mws])
  have w24 : W1 24 = BitVec.ofNat 64 p.1.db := hw (24, BitVec.ofNat 64 p.1.db) (by simp [mws])
  refine WP.seq (WP.mono (clearBlock_ok hH I.L R1) fun u1 ⟨L1, k1, hcx1, R1'⟩ => ?_)
  refine WP.mono (copyH_ok hH L1 R1' hm.2 w23 w24 hcx1) fun u2 ⟨L2, k2, R2⟩ =>
    ⟨hm, hj, L2, k2.2.2.trans (k1.2.2.trans (I.wr.trans hwr)), ⟨_, _, R2, hw, fun i h1 h2 => ?_⟩, fun q hq => ?_⟩
  · simp only [cpV, clrV]
    rw [ifn (by omega), ifp (by omega)]
  · rw [List.mem_singleton.mp hq]
    show u2.gpr .rcx = off p.1.S oY
    exact (k2.gpr (by decide)).trans hcx1

include hH in
theorem counter_ct (hc : HashChecks H.P H.D n) : RelCT isa (Two (M1 H n)) (.block (counter H)) (Two (M2 H n)) := by
  obtain ⟨_, hp⟩ := hc.counter
  refine two_post (two_pub n [31] [.rcx] (fun p => p.1.F) (fun p => p.1.S) (fun p => p.1.rest)
    (fun p => [(31, BitVec.ofNat 64 p.2)]) (fun p => [(.rcx, off p.1.S oY)])
    (fun p t h => ⟨_, h.2.2.sub (fun q hq => by rw [List.mem_singleton.mp hq]; simp [mws]) (fun _ h => h)
      fun _ _ x => x⟩)
    (fun p t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun p t h => ?_
  obtain ⟨hm, hj, P⟩ := h
  obtain ⟨V, W, R, hw, hz⟩ := P.W
  have hD := hH.hD0
  have hfit := hm.2.fit
  have c1 : oEm = 2560 := rfl
  have hjD : p.2 ≤ p.2 * H.D := Nat.le_mul_of_pos_right _ hD
  refine WP.mono (counter_ok hH P.L R (hw (31, BitVec.ofNat 64 p.2) (by simp [mws])) (by omega)
    (P.regs (.rcx, _) (by simp))) fun u ⟨L', k, R'⟩ => ⟨hm, hj, P.next L' k.2.2 R' (fun q hq => ?_) ⟨by simp [upd],
      fun i h1 h2 => ?_⟩⟩
  · rcases List.mem_append.mp hq with hq | hq
    · have := mws_keys hq
      simp only [upd]
      rw [ifn (by omega), ifn (by omega)]
      exact hw q hq
    · rw [List.mem_singleton.mp hq]; simp [upd]
  · simp only [ctrV]
    rw [ifn (by omega)]
    exact hz i (by omega) h2

/-- The anchor of the hash in round `p`. -/
def mHA (H : Hash) (p : MA × Nat) : HA := ⟨p.1.F, p.1.S, p.1.rest, mgfNb H⟩

include hH K in
theorem hash_ct (hc : HashChecks H.P H.D n) (hfx : FixedChecks n) :
    RelCT isa (Two (M2 H n)) (ctHash H) (Two (M3 H n)) := by
  obtain ⟨hnb1, hnb2⟩ := mgfNb_spec hH
  refine two_post (two_map (mHA H) (fun p t h => ⟨⟨h.1.1, by simp only [mHA]; exact Nat.succ_pos _, by simp only [mHA]; omega⟩,
    h.2.2.sub (fun q hq => by
      simp only [hws, mHA, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp [mws]) (fun _ h => h) fun _ _ ⟨h27, _⟩ => ⟨H.D + 4, h27, by simp only [mHA]; omega⟩⟩)
    (ctHash_ct hH K n hc hfx)) fun p t h => ?_
  obtain ⟨hm, hj, P⟩ := h
  obtain ⟨V, W, R, hw, h27, hz⟩ := P.W
  refine WP.mono (ctHash_ok hH K P.L R (msg := (List.range (H.D + 4)).map fun i => V (oY + i)) (nbm := mgfNb H)
    (by simp [h27]) (hw (28, BitVec.ofNat 64 (mgfNb H)) (by simp)) (by simp; omega) (by omega) fun i hi => ?_)
    fun u ⟨L', _, hwr, _, V', W', R', _, hW', _⟩ =>
      ⟨hm, hj, P.next L' hwr R' (fun q hq => ?_) trivial⟩
  · by_cases h : i < H.D + 4
    · simp [List.getD_eq_getElem?_getD, h]
    · rw [hz i (by omega) hi]
      simp [List.getD_eq_getElem?_getD, h]
  · have := mws_keys hq
    rw [hW' q.1 (by unfold nW frameBytes; omega) (by omega) (by omega)]
    exact hw q (List.mem_append_left _ hq)

include hH in
theorem xorOut_ct (hc : HashChecks H.P H.D n) : RelCT isa (Two (M3 H n)) (xorOut H) (Two (M4 H n)) := by
  obtain ⟨_, hp⟩ := hc.xorOut
  refine two_post (two_pub n [21, 23, 24, 32] [] (fun p => p.1.F) (fun p => p.1.S) (fun p => p.1.rest)
    (fun p => [(21, p.1.S), (23, off p.1.S p.1.e), (24, BitVec.ofNat 64 p.1.db), (32, BitVec.ofNat 64 (p.2 * H.D))])
    (fun _ => [])
    (fun p t h => ⟨_, h.2.2.sub (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp [mws]) (fun _ h => h) fun _ _ x => x⟩)
    (fun p t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun p t h => ?_
  obtain ⟨hm, hj, P⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := P.W
  exact WP.mono (xorOut_ok hH P.L R hm.2 (hw (23, off p.1.S p.1.e) (by simp [mws])) (hw (24, BitVec.ofNat 64 p.1.db) (by simp [mws]))
    (hw (32, BitVec.ofNat 64 (p.2 * H.D)) (by simp [mws])) hj) fun u ⟨L', k, R'⟩ => ⟨hm, P.next L' k.2.2 R' hw trivial⟩

theorem nextCtr_ct (hc : HashChecks H.P H.D n) : RelCT isa (Two (M4 H n)) (.block (nextCtr H)) fun _ _ => True := by
  obtain ⟨_, hp⟩ := hc.nextCtr
  exact two_pub n [24, 31, 32] [] (fun p => p.1.F) (fun p => p.1.S) (fun p => p.1.rest)
    (fun p => [(24, BitVec.ofNat 64 p.1.db), (31, BitVec.ofNat 64 p.2), (32, BitVec.ofNat 64 (p.2 * H.D))])
    (fun _ => [])
    (fun p t h => ⟨_, h.2.sub (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp [mws]) (fun _ h => h) fun _ _ x => x⟩)
    (fun p t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp

include hH K in
theorem round_ct (hc : HashChecks H.P H.D n) (hfx : FixedChecks n) :
    RelCT isa (Two (MB H n G))
      (seqs [clearBlock H, copyH H, .block (counter H), ctHash H, xorOut H, .block (nextCtr H)]) fun _ _ => True := by
  simp only [seqs]
  exact RelCT.assoc ((clearCopy_ct hH n hc).seq ((counter_ct hH n hc).seq ((hash_ct hH K n hc hfx).seq
    ((xorOut_ct hH n hc).seq (nextCtr_ct n hc)))))

include hH K hGh hGl hG in
theorem round_wp {a : MA} {j : Nat} {t : State} (h : MI H n G a j t) :
    WP isa (seqs [clearBlock H, copyH H, .block (counter H), ctHash H, xorOut H, .block (nextCtr H)]) t fun t' =>
      isa.eval .b t' = some (decide (j + 1 < mN H.D a)) ∧ (j + 1 < mN H.D a → MI H n G a (j + 1) t') ∧
      (j + 1 = mN H.D a → True) := by
  have hD := hH.hD0
  obtain ⟨hm, hjD, u₀, V, W, hwr, h21, h23, h24, I⟩ := h
  refine WP.mono (round_ok hH K hGh hGl hG hm.2 h23 h24 I hjD) fun t' ⟨hcf, I'⟩ => ⟨?_, fun h' =>
    ⟨hm, (cnt_iff hD).mp h', u₀, V, W, hwr, h21, h23, h24, I'⟩, fun _ => trivial⟩
  simp only [eval, hcf, Option.some.injEq, decide_eq_decide]
  exact (cnt_iff hD).symm

include hH K hGh hGl hG in
/-- `mgfXor` is constant time. -/
theorem mgfXor_ct (hc : HashChecks H.P H.D n) (hfx : FixedChecks n) :
    RelCT isa (Two (ME H n)) (mgfXor H) fun _ _ => True :=
  (mgfInit_ct hH n (G := G) hfx).seq ((two_loop (Φ := MI H n G) (Ψ := fun _ _ => True) (mN H.D)
    (round_ct hH K n hc hfx) fun _ _ _ _ h => round_wp hH K n hGh hGl hG h).mono (fun _ _ h => h)
    fun _ _ _ => trivial)

end VG.Proof.RsaPss.X86_64
