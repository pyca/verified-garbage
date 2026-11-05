module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Loop
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Reduce
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Deterministic ECDSA on x86 (32-bit): correctness

The loop leaves it at a candidate that is suitable or the last (`loop_ok`);
before it, `h`, `K`, `V`, `core`'s digest and the count are as RFC 6979's
steps a–g make them (`stageB_ok` … `stageE_ok`); and the signature of that
candidate is RFC 6979's (`result_eq`), for the hash function `P`'s instance
of the contract.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)

variable {P : RfcHash} {L : Lay P.I.hashLen} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## The frame's entry -/

section Entry

open VG.X86.Wp

variable {cs : List (String × List (BitVec 64))} {I : Proof.Ecdsa.Rfc6979.Instance}
  {H : Impl.Pbkdf2.Whole.X86.Fns} {f : Fns} {ns : List String} {s : State}

/-- A word of the stack, through a store elsewhere in it. -/
theorem stk_sep (B : Addr) (m : Mem) {x y : Nat} (v : BitVec 32)
    (h : x + 4 ≤ y ∨ y + 4 ≤ x) (hx : x + 4 ≤ 616) (hy : y + 4 ≤ 616) :
    (m.writeW (B + BitVec.ofNat 64 y) v).readW (B + BitVec.ofNat 64 x) 32 = m.readW (B + BitVec.ofNat 64 x) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega_arith) (by omega_arith)) (by decide)

/-- Our caller's registers, `hmac`'s address, and its `D` and `B` in the
frame: `Ctx` holds. -/
theorem entry_ok (h : (rfcX86 cs I 588 (tabFacts H f) ns).pre s) :
    WP isa (.block Cfg.entry) (entered s) fun t₁ => t₁.gpr .eax = arg s 5 ∧
      t₁.gpr .esp = (lay I.hashLen I.ecdsa.curve.len cs H f s).F ∧
      WP isa (.block Cfg.tabDB) t₁ (Ctx (lay I.hashLen I.ecdsa.curve.len cs H f s) s.gpr s.mem) := by
  have hL := lay_ok h
  have nB := hL.nB
  have nt : (arg s 5).toNat + 24 ≤ 2 ^ 32 := hL.nt
  have hh := h
  obtain ⟨e588, e28, hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hTb, -, -, -, -, -, -, hF⟩ := hh
  obtain ⟨tOk, tMem, tD, tB⟩ := hF
  have hesp : (entered s).gpr .esp = (lay I.hashLen I.ecdsa.curve.len cs H f s).F :=
    entered_esp _ _ cs H f s
  have hw : ∀ o, o + 4 ≤ 512 → InRegions (entered s).wr (addr (lay I.hashLen I.ecdsa.curve.len cs H f s).F o) 4 :=
    fun o ho => ⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).FR, by rw [entered_wr h]; simp, by
      rw [hL.addrF (by omega_arith)]; exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)⟩
  have hg : ∀ r, r ≠ .esp → (entered s).gpr r = s.gpr r := fun r hr => allocState_gpr _ _ hr
  have a : ∀ o, o < 540 → addr (lay I.hashLen I.ecdsa.curve.len cs H f s).F o =
      (lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 (76 + o) := fun o ho => hL.addrF ho
  have hA : ∀ i < 6, (lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 (592 + 4 * i) = argAddr s i :=
    fun i hi => (lay_argAddr e588 e28 hi).symm
  -- The table's words, apart from the stack.
  have hTab : ∀ o, o + 4 ≤ 24 → (lay I.hashLen I.ecdsa.curve.len cs H f s).TAB.Contains
      (addr (arg s 5) o) (32 / 8) := fun o ho => by
    rw [addr_eq (by omega_arith)]; exact Offset.contains_base _ ho (by omega_arith)
  simp only [Cfg.entry, saved, fSave, List.map_cons, List.map_nil, List.cons_append, List.nil_append, stk,
    Nat.reduceAdd]
  refine wp_stm hesp (hw 128 (by omega_arith)) fun s₁ u₁ => ?_
  refine wp_stm (B := (lay I.hashLen I.ecdsa.curve.len cs H f s).F) (by rw [u₁.gpr, hesp])
    (by rw [u₁.wr]; exact hw 132 (by omega_arith)) fun s₂ u₂ => ?_
  refine wp_stm (B := (lay I.hashLen I.ecdsa.curve.len cs H f s).F) (by rw [u₂.gpr, u₁.gpr, hesp])
    (by rw [u₂.wr, u₁.wr]; exact hw 136 (by omega_arith)) fun s₃ u₃ => ?_
  refine wp_stm (B := (lay I.hashLen I.ecdsa.curve.len cs H f s).F) (by rw [u₃.gpr, u₂.gpr, u₁.gpr, hesp])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hw 140 (by omega_arith)) fun s₄ u₄ => ?_
  have esp₄ : s₄.gpr .esp = (lay I.hashLen I.ecdsa.curve.len cs H f s).F := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hesp]
  have m₄ : s₄.mem = (((s.mem.writeW ((lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 204) (s.gpr .ebx)).writeW
      ((lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 208) (s.gpr .esi)).writeW
      ((lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 212) (s.gpr .edi)).writeW
      ((lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 216) (s.gpr .ebp) := by
    simp only [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.gpr]
    rw [a 128 (by omega_arith), a 132 (by omega_arith), a 136 (by omega_arith), a 140 (by omega_arith),
      hg .ebx (by decide), hg .esi (by decide), hg .edi (by decide), hg .ebp (by decide)]
    rfl
  have ct : ∀ x, 204 ≤ x → x + 4 ≤ 228 → (⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 204, 24⟩ :
      Region).Contains ((lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 x) (32 / 8) :=
    fun x h₁ h₂ => Offset.contains _ h₁ (by omega_arith) (by omega_arith)
  have hf₄ : Frame [⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 204, 24⟩] s.mem s₄.mem := by
    rw [m₄]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ct 204 (by omega_arith) (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (ct 208 (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
      (ct 212 (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _ (ct 216 (by omega_arith) (by omega_arith))
  have tabD : ∀ r ∈ [(⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 204, 24⟩ : Region)],
      Region.Disjoint (lay I.hashLen I.ecdsa.curve.len cs H f s).TAB r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hL.tk.sub_right (Offset.sub_base _ (by omega_arith))
  -- `eax = hmac`.
  refine wp_ldm (B := (lay I.hashLen I.ecdsa.curve.len cs H f s).F) (o := 512 + 4 + 4 * 5) esp₄
    ⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).ARGS, by
      rw [u₄.rd, u₄.wr, u₃.wr, u₂.wr, u₁.wr, entered_wr h, hwr, lay_ARGS e588 e28]; simp, by
      rw [a _ (by omega_arith)]; exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)⟩
    fun s₅ u₅ => WP.block_nil ?_
  have eax₅ : s₅.gpr .eax = arg s 5 := by
    rw [u₅.gpr, a _ (by omega_arith), show 76 + (512 + 4 + 4 * 5) = 592 + 4 * 5 from rfl, hA 5 (by decide)]
    exact hf₄.readW (r := (lay I.hashLen I.ecdsa.curve.len cs H f s).ARGS)
      (by rw [← hA 5 (by decide)]; exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide)
  refine ⟨eax₅, by rw [u₅.other _ (by decide), esp₄], ?_⟩
  -- `D` and `B`.
  simp only [Cfg.tabDB, stk, fDl, fBl, VG.Impl.Pbkdf2.Stream.X86.at_]
  have hrd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; rfl
  have hwr₅ : s₅.wr = (entered s).wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have inTab : ∀ o, o + 4 ≤ 24 → InRegions (s₅.rd ++ s₅.wr) (addr (arg s 5) o) 4 := fun o ho =>
    ⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).TAB, by rw [hrd₅, hrd]; simp [Lay.TAB, Lay.tab, lay], hTab o ho⟩
  refine wp_ldm eax₅ (inTab 16 (by omega_arith)) fun s₆ u₆ => ?_
  refine wp_stm (B := (lay I.hashLen I.ecdsa.curve.len cs H f s).F)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), esp₄])
    (by rw [u₆.wr, hwr₅]; exact hw 144 (by omega_arith)) fun s₇ u₇ => ?_
  refine wp_ldm (B := arg s 5) (by rw [u₇.gpr, u₆.other _ (by decide), eax₅])
    (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr]; exact inTab 20 (by omega_arith)) fun s₈ u₈ => ?_
  refine wp_stm (B := (lay I.hashLen I.ecdsa.curve.len cs H f s).F)
    (by rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), esp₄])
    (by rw [u₈.wr, u₇.wr, u₆.wr, hwr₅]; exact hw 148 (by omega_arith)) fun s₉ u₉ => WP.block_nil ?_
  -- The table's words, as on entry.
  have tw : ∀ o, o + 4 ≤ 24 → s₄.mem.readW (addr (arg s 5) o) 32 = s.mem.readW (addr (arg s 5) o) 32 :=
    fun o ho => hf₄.readW (hTab o ho) tabD (by decide)
  have vD : s₆.gpr .ecx = BitVec.ofNat 32 H.H.D := by rw [u₆.gpr, u₅.mem, tw 16 (by omega_arith), tD]
  have m₇ : s₇.mem = s₄.mem.writeW ((lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 220)
      (BitVec.ofNat 32 H.H.D) := by rw [u₇.mem, u₆.mem, u₅.mem, vD, a 144 (by omega_arith)]
  have hf₇ : Frame [⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 204, 24⟩] s.mem s₇.mem := by
    rw [m₇]; exact hf₄.writeW (List.mem_singleton_self _) _ (ct 220 (by omega_arith) (by omega_arith))
  have vB : s₈.gpr .ecx = BitVec.ofNat 32 H.H.B := by
    rw [u₈.gpr, hf₇.readW (hTab 20 (by omega_arith)) tabD (by decide), tB]
  have m₉ : s₉.mem = s₇.mem.writeW ((lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 224)
      (BitVec.ofNat 32 H.H.B) := by rw [u₉.mem, u₈.mem, vB, a 148 (by omega_arith)]
  have hf₉ : Frame [⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 204, 24⟩] s.mem s₉.mem := by
    rw [m₉]; exact hf₇.writeW (List.mem_singleton_self _) _ (ct 224 (by omega_arith) (by omega_arith))
  have sy₉ : s₉.syms = s.syms := by
    rw [u₉.syms, u₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]; rfl
  refine
    { rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, hrd₅, hrd, lay_tbls]; rfl
      wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, hwr₅, entered_wr h, hwr, lay_ARGS e588 e28]; rfl
      esp := by rw [u₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), esp₄]
      saved := fun p hp => ?_
      pArg := fun i hi => ?_
      pDl := by
        rw [m₉, stk_sep _ _ _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith), m₇,
          Mem.readW_writeW_self32]; rfl
      pBl := by rw [m₉, Mem.readW_writeW_self32]; rfl
      frame := hf₉.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).STK, by simp,
          Offset.sub_base (d := 204) (n := 24) (k := 588) _ (by omega_arith)⟩
      sy := fun c hc => by rw [sy₉]; exact (lay_sy s hc).symm
      held := fun c hc => by
        change c ∈ cs at hc
        simpa only [lay_sy s hc] using hTb.1 c hc
      tabOk := by rw [sy₉]; exact tOk
      tabMem := by rw [sy₉]; exact tMem
      fsy := fun n hn => by rw [sy₉]; exact (ite_eq_left hn).symm }
  · simp only [saved, fSave, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> dsimp only [Nat.reduceAdd]
    · rw [m₉, stk_sep _ _ _ (x := 204) (y := 224) (by omega_arith) (by omega_arith) (by omega_arith), m₇, stk_sep _ _ _ (x := 204) (y := 220) (by omega_arith) (by omega_arith) (by omega_arith), m₄, stk_sep _ _ _ (x := 204) (y := 216) (by omega_arith) (by omega_arith) (by omega_arith), stk_sep _ _ _ (x := 204) (y := 212) (by omega_arith) (by omega_arith) (by omega_arith), stk_sep _ _ _ (x := 204) (y := 208) (by omega_arith) (by omega_arith) (by omega_arith), Mem.readW_writeW_self32]
    · rw [m₉, stk_sep _ _ _ (x := 208) (y := 224) (by omega_arith) (by omega_arith) (by omega_arith), m₇, stk_sep _ _ _ (x := 208) (y := 220) (by omega_arith) (by omega_arith) (by omega_arith), m₄, stk_sep _ _ _ (x := 208) (y := 216) (by omega_arith) (by omega_arith) (by omega_arith), stk_sep _ _ _ (x := 208) (y := 212) (by omega_arith) (by omega_arith) (by omega_arith), Mem.readW_writeW_self32]
    · rw [m₉, stk_sep _ _ _ (x := 212) (y := 224) (by omega_arith) (by omega_arith) (by omega_arith), m₇, stk_sep _ _ _ (x := 212) (y := 220) (by omega_arith) (by omega_arith) (by omega_arith), m₄, stk_sep _ _ _ (x := 212) (y := 216) (by omega_arith) (by omega_arith) (by omega_arith), Mem.readW_writeW_self32]
    · rw [m₉, stk_sep _ _ _ (x := 216) (y := 224) (by omega_arith) (by omega_arith) (by omega_arith), m₇, stk_sep _ _ _ (x := 216) (y := 220) (by omega_arith) (by omega_arith) (by omega_arith), m₄, Mem.readW_writeW_self32]
  · rw [hf₉.readW (r := ⟨(lay I.hashLen I.ecdsa.curve.len cs H f s).B + BitVec.ofNat 64 (592 + 4 * i), 4⟩)
      (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide),
      hA i hi, lay_a s i hi]
    rfl

end Entry

/-! ## The loop -/

theorem tries_ok (hL : L.Ok) (hk : CoreOk P L) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) (h0 : LoopInv P L m₀ 0 t) :
    WP isa (.loop (cfgOf P).tryOne .ne) t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' := by
  refine WP.loop (M := isa) (fun n (s : State) => Ctx L g m₀ s ∧ LoopInv P L m₀ (P.I.tries - n) s ∧ n ≤ P.I.tries)
    ?_ P.I.tries t
    ⟨hc, by rw [Nat.sub_self]; exact h0, Nat.le_refl _⟩
  rintro n s ⟨hcs, hi, hn⟩
  have hn1 : 1 ≤ n := by have := hi.lt; omega_using [this]
  refine WP.mono (tryOne_ok hL hk hT hcs hi) fun s' ⟨hc', h⟩ => ?_
  rcases h with ⟨he, hx⟩ | ⟨he, hx⟩
  · exact .inl ⟨he, hc', _, hx⟩
  · refine .inr ⟨he, n - 1, by omega_using [hn1], hc', ?_, by omega_using [hn]⟩
    rwa [show P.I.tries - (n - 1) = P.I.tries - n + 1 by omega_using [hn, hn1]]

/-! ## Steps a–g -/

/-- `rlen` is the scalars' `Q` bytes. -/
theorem rlen_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.rlen P.R.E.C = P.Q := by
  have := P.R.nBits_len
  exact rlenR (by show _ ≤ 8 * P.R.E.C.len; omega_using [this]) (by show 8 * P.R.E.C.len < _; omega_using [this])

/-- RFC 6979's `K` and `V` after step g, from the code's. -/
theorem kv0_eq (P : RfcHash) {x : Nat} {dB hB h : List Byte} (hd : dB.length = P.Q)
    (hx : x = Spec.Weierstrass.ofBytes dB) (hh : Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C hB = h) :
    Spec.Ecdsa.Rfc6979.init P.R.E.C P.ok.hH.SH.H P.F.H.D x hB =
      let K₁ := P.mac (List.replicate P.F.H.D 0) (List.replicate P.F.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB ++ h))
      let V₁ := P.mac K₁ (List.replicate P.F.H.D 1)
      let K₂ := P.mac K₁ (V₁ ++ [BitVec.ofNat 8 1] ++ (dB ++ h))
      (K₂, P.mac K₂ V₁) := by
  have hi : Spec.Ecdsa.Rfc6979.int2octets P.R.E.C x = dB := by
    rw [Spec.Ecdsa.Rfc6979.int2octets, rlen_eq, hx, ← hd, toBytes_ofBytes]
  simp only [Spec.Ecdsa.Rfc6979.init, hi, hh, List.append_assoc, List.singleton_append]
  rfl

/-- `h`, RFC 6979's `bits2octets` of the digest. -/
abbrev hSpec (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C (hBOf P L m₀)
abbrev dB (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.d P.Q

/-- `K` and `V` after steps d and e. -/
abbrev K₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  P.mac (List.replicate P.F.H.D 0) (List.replicate P.F.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB P L m₀ ++ hSpec P L m₀))
abbrev V₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte := P.mac (K₁ P L m₀) (List.replicate P.F.H.D 1)

/-- After step c: `h`, `V = 0x01…`, `K = 0x00…` and `core`'s digest. -/
structure QB (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = List.replicate P.F.H.D 0
  v : vOf P L u.mem = List.replicate P.F.H.D 1
  dg : DgOk P L m₀ u.mem

/-- After step e. -/
structure QC (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = K₁ P L m₀
  v : vOf P L u.mem = V₁ P L m₀
  dg : DgOk P L m₀ u.mem
  saved : SavedK P L u.mem (kOf P L u.mem)

/-- After step g. -/
structure QD (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  k : kOf P L u.mem = (kv0 P L m₀).1
  v : vOf P L u.mem = (kv0 P L m₀).2
  dg : DgOk P L m₀ u.mem
  saved : SavedK P L u.mem (kOf P L u.mem)

theorem kv0_eq' (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) :
    kv0 P L m₀ = (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀)),
      P.mac (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀))) (V₁ P L m₀)) :=
  kv0_eq P (length_bytesAt _ _ _) rfl rfl

/-- The digest's integer is `X`'s, `Q - m` zero bytes then the digest's first
`m = min(D, Q)`, if the scalars have `8 Q` bits. -/
theorem x_eq {C : Spec.Weierstrass.Curve} {Q D : Nat} (hq : Spec.Ecdsa.nBits C = 8 * Q) (hn : C.n ≠ 0)
    {hB : List Byte} (hl : hB.length = D) :
    Spec.Weierstrass.ofBytes (List.replicate (Q - min D Q) 0 ++ hB.take (min D Q)) = Spec.Ecdsa.hashToInt C hB := by
  by_cases h : Q ≤ D
  · rw [Nat.min_eq_right h, Nat.sub_self, List.replicate_zero, List.nil_append,
      hashToInt_takeQ hq (by rw [hl]; exact h)]
  · rw [Nat.min_eq_left (by omega), List.take_of_length_le (by rw [hl]), ofBytes_zeros,
      (hashToInt_short (by rw [hl, hq]; omega) hn).1]

/-- After `X` and `h`: `h`, and `core`'s digest. -/
structure QA (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  dg : DgOk P L m₀ u.mem

/-- After `X`: `Q - m` zero bytes, then the digest's first `m = min(D, Q)`. -/
abbrev QX (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop :=
  Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (76 + fX)) P.Q =
    List.replicate (P.Q - min P.F.H.D P.Q) 0 ++ (hBOf P L m₀).take (min P.F.H.D P.Q)

theorem stageX_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) :
    WP isa (cfgOf P).prepX u fun u' => Ctx L g m₀ u' ∧ QX P L m₀ u' := by
  have hD : P.F.H.D = P.I.hashLen := P.len.symm
  obtain ⟨-, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  have hdg : Spec.Sha256.bytesAt u.mem L.dg (min P.F.H.D P.Q) =
      (hBOf P L m₀).take (min P.F.H.D P.Q) := by
    rw [hc.dgBytes hL (by rw [← hD]; omega), hBOf, ← bytesAt_take _ _ (Nat.min_le_left _ _)]
  exact WP.mono (prepX_ok hL hT (by rw [← hD]) hc) fun u₁ ⟨hc₁, _, hx₁⟩ => ⟨hc₁, by show Spec.Sha256.bytesAt _ _ _ = _; rw [hx₁, hdg]⟩

/-- `h` (step c's `h1` as `bits2octets`), and `core`'s digest. -/
theorem stageH_ok (hL : L.Ok) (hT : TabL P L) {u₁ : State} (hc₁ : Ctx L g m₀ u₁) (hx₁ : QX P L m₀ u₁) :
    WP isa (cfgOf P).prepH u₁ fun u' => Ctx L g m₀ u' ∧ QA P L m₀ u' := by
  have hD : P.F.H.D = P.I.hashLen := P.len.symm
  have hl := P.R.nBits_len
  obtain ⟨-, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  have hlB : (hBOf P L m₀).length = P.F.H.D := length_bytesAt _ _ _
  unfold QX at hx₁
  cases hb : P.R.big
  · have hq : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := (P.R.sizesA hb).2.2.1
    have hX : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u₁.mem (xa L) P.Q) = eOf P L m₀ := by
      rw [show xa L = L.B + BitVec.ofNat 64 (76 + fX) from rfl, hx₁, x_eq hq P.R.n_ne hlB]
    rw [show (cfgOf P).prepH = .block (cfgOf P).reduce by simp only [Cfg.prepH, show (cfgOf P).big = false from hb,
      Bool.false_eq_true, ite_false]]
    obtain ⟨hQk, -, hQ64⟩ := P.sizesA hb
    refine WP.mono (reduce_ok hb hL hc₁) fun u₂ ⟨hc₂, hf₂, hh₂⟩ => ⟨hc₂, ?_, ?_⟩
    · rw [← hQk] at hh₂
      show Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (76 + (cfgOf P).fHo)) P.Q = _
      rw [show (cfgOf P).fHo = fH by simp only [Cfg.fHo, show (cfgOf P).big = false from hb, Bool.false_eq_true,
        ite_false], show 76 + fH = hB from rfl]
      conv_lhs => rw [← toBytes_ofBytes (Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 hB) P.Q)]
      rw [length_bytesAt, hh₂, hX, hSpec, Spec.Ecdsa.Rfc6979.bits2octets,
        Spec.Ecdsa.Rfc6979.int2octets, Spec.Ecdsa.Rfc6979.bits2int, rlen_eq]
    · unfold DgOk
      simp only [dgAddr, Cfg.fDg, show (cfgOf P).big = false from hb, Bool.false_eq_true, ite_false]
      have := hL.nB
      have hfX : fX = 232 := rfl
      have hhB : hB = 236 := rfl
      rw [bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
          · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) (by omega),
        hashToInt_takeQ hq (by rw [length_bytesAt]), List.take_of_length_le (by rw [length_bytesAt])]
      exact hX
  · obtain ⟨-, hQ66', -, hQD⟩ := P.sizesW hb
    have hN : 8 * P.F.H.D < Spec.Ecdsa.nBits P.R.E.C := by
      have : P.F.H.D < P.R.E.C.len := hQD
      omega
    have hm : min P.F.H.D P.Q = P.F.H.D := Nat.min_eq_left (by omega)
    rw [hm, List.take_of_length_le (by rw [hlB])] at hx₁
    rw [show (cfgOf P).prepH = (cfgOf P).prepC by simp only [Cfg.prepH, show (cfgOf P).big = true from hb, ite_true]]
    refine WP.mono (prepC_ok hL hT hb (by rw [← hD]) hc₁) fun u₂ ⟨hc₂, hf₂, hx₂⟩ => ⟨hc₂, ?_, ?_⟩
    · show Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (76 + (cfgOf P).fHo)) P.Q = _
      rw [show (cfgOf P).fHo = fX by simp only [Cfg.fHo, show (cfgOf P).big = true from hb, ite_true],
        bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hL.stk_scr (by simp only [fX]; omega) (by decide)
          · exact Offset.disjoint _ (.inl (by simp only [fX, fXc]; omega)) (by simp only [fX]; omega)
              (by simp only [fXc]; omega)) (by omega),
        hx₁, hSpec, bits2octets_short (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega)
          (by show 8 * P.R.E.C.len < _; omega) (by rw [hlB]; exact hN) P.R.n_ne, hlB]
    · -- `core`'s digest: the digest's number `e`, shifted left by `sh` bits.
      have e₂ : eOf P L m₀ = Spec.Weierstrass.ofBytes (hBOf P L m₀) :=
        (hashToInt_short (by rw [hlB]; exact hN) P.R.n_ne).1
      rw [hc₁.dgBytes hL (by rw [← hD])] at hx₂
      have hlt : Spec.Weierstrass.ofBytes (hBOf P L m₀) * 2 ^ P.R.sh < 2 ^ (8 * P.Q) := by
        have := ofBytes_lt (hBOf P L m₀)
        rw [hlB] at this
        calc _ < 2 ^ (8 * P.F.H.D) * 2 ^ P.R.sh := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
          _ ≤ 2 ^ (8 * P.Q) := by
            rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by simp only [RfcHash.Q]; omega)
      have hl₁ : (Spec.Weierstrass.toBytes P.Q (Spec.Weierstrass.ofBytes (hBOf P L m₀) * 2 ^ P.R.sh)).length = P.Q := by
        simp [Spec.Weierstrass.toBytes]
      unfold DgOk
      simp only [dgAddr, Cfg.fDg, show (cfgOf P).big = true from hb, ite_true]
      rw [hx₂, hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega) (by rw [hl₁]),
        List.take_of_length_le (by rw [hl₁]), ofBytes_toBytes _ _ hlt,
        show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = P.R.sh from hl.2.2.symm, Nat.shiftRight_eq_div_pow,
        Nat.mul_div_cancel _ (Nat.two_pow_pos _), e₂]

/-- `h` in the message, kept by the steps on `K` and `V`. -/
theorem hOf_frame (hL : L.Ok) {ws : List Region} {m m' : Mem} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, r = L.SCR ∨ r = ⟨L.B, 204⟩ ∨ ∃ o n, r = ⟨L.B + BitVec.ofNat 64 o, n⟩ ∧ o + n ≤ 76 + fH) :
    hOf P L m' = hOf P L m := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hQ66, -, -⟩ := P.sizes
  have := hL.nB
  have hho : 76 + fH ≤ 76 + (cfgOf P).fHo ∧ 76 + (cfgOf P).fHo + P.Q ≤ 76 + fXc := by
    simp only [Cfg.fHo]; split <;> simp only [fH, fX, fXc] <;> omega
  refine bytesAt_frame hf (fun r hr => ?_) (by omega)
  rcases hd r hr with rfl | rfl | ⟨o, n, rfl, hon⟩
  · exact hL.stk_SCR (by simp only [fXc] at hho; omega)
  · exact Offset.disjoint_base _ (by simp only [fH] at hho; omega) (by simp only [fXc] at hho; omega)
  · exact Offset.disjoint _ (.inr (by omega)) (by simp only [fXc] at hho; omega) (by simp only [fH] at hon; omega)

theorem hOf_kvw (hL : L.Ok) {m m' : Mem} (hf : Frame (KVW L) m m') : hOf P L m' = hOf P L m :=
  hOf_frame hL hf fun r hr => by
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)

/-- `V = 0x01…` and `K = 0x00…`. -/
theorem stageB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hq : QA P L m₀ u) :
    WP isa (.block Cfg.initKV) u fun u' => Ctx L g m₀ u' ∧ QB P L m₀ u' := by
  obtain ⟨-, -, -, -, -, hD64, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  exact WP.mono (initKV_ok hL hc) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
    ⟨hc₂, ⟨(hOf_frame hL hf₂ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact .inr (.inr ⟨76, 128, rfl, by simp only [fH]; omega⟩)).trans hq.h,
      hk₂ _ hD64, hv₂ _ hD64, hq.dg.frameOf hL hf₂ (by simp [DgApart])⟩⟩

theorem stageC_ok (hL : L.Ok) (hk : CoreOk P L) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) (hq : QB P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 0) u fun u' => Ctx L g m₀ u' ∧ QC P L m₀ u' :=
  WP.mono (rekeyFull_ok hL (hok_of hk hT) hc 0 fun h => absurd rfl h) fun u' ⟨hc', hf', hk', hv', hS'⟩ =>
    ⟨(hOf_kvw hL hf').trans hq.h,
      by rw [hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hf' kvw_apart, hS'⟩ |>
    fun h => ⟨hc', h⟩

theorem stageD_ok (hL : L.Ok) (hk : CoreOk P L) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) (hq : QC P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 1) u fun u' => Ctx L g m₀ u' ∧ QD P L m₀ u' :=
  WP.mono (rekeyFull_ok hL (hok_of hk hT) hc 1 fun _ => hq.saved) fun u' ⟨hc', hf', hk', hv', hS'⟩ =>
    ⟨hc', by rw [kv0_eq', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [kv0_eq', hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hf' kvw_apart, hS'⟩

theorem stageE_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hq : QD P L m₀ u) :
    WP isa (.block (cfgOf P).initCnt) u fun u' => Ctx L g m₀ u' ∧ LoopInv P L m₀ 0 u' :=
  have := hL.nB
  have hD64 : P.F.H.D ≤ 64 := P.sizes.2.2.2.2.2.1
  WP.mono (initCnt_ok hL hc) fun u' ⟨hc', hf', hn'⟩ => ⟨hc', P.tries_pos,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega))
      (by omega)).trans hq.k,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega))
      (by omega)).trans hq.v,
    by rw [hn', Nat.sub_zero], fun j hj => absurd hj (Nat.not_lt_zero _), hq.dg.frameOf hL hf' (by simp [DgApart]),
    by
      have hk' : kOf P L u'.mem = kOf P L u.mem := bytesAt_frame hf' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by omega)
      rw [hk']
      exact hq.saved.frame hf' fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hL.stk_scr (d := 232) (n := 4) (by omega) (by decide)).symm⟩

theorem stageG_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) {i : Nat}
    (hx : Exit P L m₀ i u) :
    WP isa (.block Cfg.wipe) u fun u' => Ctx L g m₀ u' ∧ Exit P L m₀ i u' ∧ ∀ p ∈ saved, u'.gpr p.1 = g p.1 :=
  have hQ66 : P.Q ≤ 66 := P.sizes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  WP.mono (wipe_ok hL hc) fun _ ⟨hc₇, ha₇, hf₇, hs₇⟩ => ⟨hc₇, ⟨hx.lt, hx.fails, hx.last,
    hx.res.keep ha₇ (bytesAt_frame hf₇ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hL.stk_OUT (d := 76) (n := 128) (by omega)).symm.sub_left (Region.sub_prefix (by rw [hk.1]))
      · exact (hL.stk_OUT (d := 228) (n := 360) (by omega)).symm.sub_left
          (Region.sub_prefix (by rw [hk.1]))) (by omega))⟩, hs₇⟩

/-- The body after the frame's entry. -/
abbrev rest (P : RfcHash) : Prog isa :=
  .seq (cfgOf P).prepX (.seq (cfgOf P).prepH (.seq (.block Cfg.initKV) (.seq ((cfgOf P).rekeyFull 0)
    (.seq ((cfgOf P).rekeyFull 1) (.seq (.block (cfgOf P).initCnt) (.seq (.loop (cfgOf P).tryOne .ne)
      (.block Cfg.wipe)))))))

theorem body_eq (P : RfcHash) : (cfgOf P).body = .seq (.block Cfg.entry) (.seq (.block Cfg.tabDB) (rest P)) := rfl

theorem rest_ok (hL : L.Ok) (hk : CoreOk P L) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (rest P) t fun t' => Ctx L g m₀ t' ∧ (∃ i, Exit P L m₀ i t') ∧ ∀ p ∈ saved, t'.gpr p.1 = g p.1 :=
  WP.seq (WP.mono (stageX_ok hL hT hc) fun _ ⟨h₀, q₀⟩ =>
    WP.seq (WP.mono (stageH_ok hL hT h₀ q₀) fun _ ⟨h₁, q₁⟩ =>
    WP.seq (WP.mono (stageB_ok hL h₁ q₁) fun _ ⟨h₂, q₂⟩ =>
      WP.seq (WP.mono (stageC_ok hL hk hT h₂ q₂) fun _ ⟨h₃, q₃⟩ =>
        WP.seq (WP.mono (stageD_ok hL hk hT h₃ q₃) fun _ ⟨h₄, q₄⟩ =>
          WP.seq (WP.mono (stageE_ok hL h₄ q₄) fun _ ⟨h₅, q₅⟩ =>
            WP.seq (WP.mono (tries_ok hL hk hT h₅ q₅) fun _ ⟨h₆, i, q₆⟩ =>
              WP.mono (stageG_ok hL hk h₆ q₆) fun _ ⟨h₇, q₇, r₇⟩ => ⟨h₇, ⟨i, q₇⟩, r₇⟩)))))))

/-! ## RFC 6979's result -/

/-- RFC 6979's number of blocks is the candidates' `V`s. -/
theorem blocks_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.F.H.D = P.nV := nV_eq P

/-- The instance's signature and number of candidates, as the proof names its parts. -/
theorem result_unfold :
    result P.I m₀ L.d L.dg =
      if 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n then
        let (K, V) := kv0 P L m₀
        Spec.Ecdsa.Rfc6979.search P.R.E.C P.ok.hH.SH.H P.F.H.D (xOf P L m₀) (eOf P L m₀) K V P.I.tries
      else (none, 0) := by
  simp only [result, Proof.Ecdsa.Rfc6979.Instance.result, P.ecdsa, P.R.curve, P.hash, P.len,
    ecdsa_bytesAt, Spec.Ecdsa.Rfc6979.sign]

/-- The signature of the candidate the loop stopped at is RFC 6979's. -/
theorem result_eq {i : Nat} {t : State} (hx : Exit P L m₀ i t) :
    (result P.I m₀ L.d L.dg).1 = sigI P L m₀ i := by
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i P.I.tries (by have := hx.lt; omega_using [this]) hx.fails,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by have := hx.lt; omega_using [this]]
    cases hs : sigI P L m₀ i with
    | some rs => rw [Proof.Ecdsa.Rfc6979.searchB_ok (blocks_eq P) hs]
    | none =>
      have h7 : i + 1 = P.I.tries := hx.last.resolve_left (by simp [hs])
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (blocks_eq P) hs, show P.I.tries - 1 - i = 0 by omega_using [h7]]
      rfl
  · symm
    simp only [hv, ite_false, sigI, Spec.Ecdsa.signWith]
    split
    · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
    · rfl

/-! ## How many candidates -/

theorem ite_le_of_not {c : Prop} [Decidable c] {a b i : Nat} (hc : ¬c) (hb : b ≤ i) :
    (if c then a else b) ≤ i := by
  simp only [hc, ite_false]; exact hb

/-- The candidate the loop stops at, from the number RFC 6979 tries. -/
def exitAt (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : Nat :=
  if (result P.I m₀ L.d L.dg).2 = 0 then P.I.tries - 1 else (result P.I m₀ L.d L.dg).2 - 1

/-- The loop goes on after candidate `i` iff it stops at a later one. -/
theorem go_iff {i : Nat} (hi : i < P.I.tries) (hf : ∀ j < i, sigI P L m₀ j = none) :
    (sigI P L m₀ i = none ∧ i + 1 < P.I.tries) ↔ i < exitAt P L m₀ := by
  unfold exitAt
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i P.I.tries (by omega_using [hi]) hf,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by omega_using [hi]]
    cases hs : sigI P L m₀ i with
    | some rs =>
      rw [Proof.Ecdsa.Rfc6979.searchB_ok (blocks_eq P) hs]
      simp
    | none =>
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (blocks_eq P) hs]
      by_cases h7 : i + 1 < P.I.tries
      · have := Proof.Ecdsa.Rfc6979.searchB_pos (C := P.R.E.C) (H := P.ok.hH.SH.H) (hlen := P.F.H.D)
          (d := xOf P L m₀) (e := eOf P L m₀) (n := P.I.tries - 2 - i)
          (K := (stepB P.ok.hH.SH.H P.nV (kvI P L m₀ i).1 (kvI P L m₀ i).2).1)
          (V := (stepB P.ok.hH.SH.H P.nV (kvI P L m₀ i).1 (kvI P L m₀ i).2).2) (blocks_eq P)
        rw [show P.I.tries - 1 - i = P.I.tries - 2 - i + 1 by omega_using [h7]]
        simp only [true_and, h7]
        simp only [kvI] at this
        rw [true_iff]
        split <;> omega
      · rw [show P.I.tries - 1 - i = 0 by omega_using [h7]]
        simp only [Spec.Ecdsa.Rfc6979.search, h7, and_false, false_iff, Nat.not_lt]
        exact ite_le_of_not (by omega_using []) (by omega_using [])
  · simp only [hv, ite_false, ite_true]
    have hs : sigI P L m₀ i = none := by
      simp only [sigI, Spec.Ecdsa.signWith]
      split
      · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
      · rfl
    simp only [hs, true_and]
    omega_using []

/-! ## The whole function -/

theorem released_gpr {s₂ : State} {r : Reg} (hr : r ≠ .esp) : (released s₂).gpr r = s₂.gpr r :=
  (Wp.Upd.setReg s₂ .esp _).other r hr

theorem released_esp (s₂ : State) : (released s₂).gpr .esp = s₂.gpr .esp + BitVec.ofNat 32 512 :=
  (Wp.Upd.setReg s₂ .esp _).gpr

/-- The contract the code for `P`'s hash function is proven against, with
`P`'s table and the functions `ns`' addresses public. -/
abbrev rfcP (P : RfcHash) (ns : List String) : Contract isa :=
  rfcX86 P.R.E.combConsts P.I 588 (tabFacts P.F P.f) ns

/-- The layout of a call from `s`. -/
abbrev layOf (P : RfcHash) (s : State) : Lay P.I.hashLen :=
  lay P.I.hashLen P.I.ecdsa.curve.len P.R.E.combConsts P.F P.f s

theorem coreOk_lay (P : RfcHash) (s : State) : CoreOk P (layOf P s) := ⟨P.curveLen, rfl⟩

theorem tabL_lay (P : RfcHash) (s : State) : TabL P (layOf P s) := ⟨rfl, rfl⟩

/-- `vg_ecdsa_<curve>_sign` for `P`'s hash function, whose body writes no
`esp`, meets `rfcP P` and keeps the callee-saved registers and its return
address. -/
theorem sign_ok {ns : List String} (hsp : NoSp (cfgOf P).body) {s : State} (h : (rfcP P ns).pre s) :
    WP isa (cfgOf P).sign s fun s' => abiPreserved s s' ∧ (rfcP P ns).post s s' := by
  have hL := lay_ok h
  have nB := hL.nB
  refine WP.alloc (by have := h.1; omega_arith) hsp ?_
  rw [body_eq]
  refine WP.seq (WP.mono (entry_ok h) fun t₁ h₁ => WP.seq (WP.mono h₁.2.2 fun t hc =>
    WP.mono (rest_ok hL (coreOk_lay P s) (tabL_lay P s) hc) fun u ⟨hu, ⟨i, hx⟩, hs⟩ => ?_))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [released_gpr (by decide)]; exact hs (.ebx, 128) (by decide)
    · rw [released_gpr (by decide)]; exact hs (.esi, 132) (by decide)
    · rw [released_gpr (by decide)]; exact hs (.edi, 136) (by decide)
    · rw [released_gpr (by decide)]; exact hs (.ebp, 140) (by decide)
    · rw [released_esp, hu.esp]; exact BitVec.sub_add_cancel _ _
  · have hret : (s.gpr .esp).setWidth 64 = (layOf P s).B + BitVec.ofNat 64 588 := by
      rw [hL.B_eq, BitVec.sub_add_cancel]; rfl
    show u.mem.readW _ 32 = _
    rw [hret]
    refine hu.frame.readW (r := (layOf P s).RET) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.ro
    · exact hL.rc
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  · show match (result P.I s.mem (layOf P s).d (layOf P s).dg).1 with
      | some rs => _ | none => _
    rw [result_eq hx]
    have e₁ : 2 * P.I.ecdsa.curve.len = 2 * P.Q := by rw [P.curveLen]
    have e₂ : P.I.ecdsa.curve = P.R.E.C := by rw [P.ecdsa, P.R.curve]
    rw [e₁]
    have hr := hx.res
    have ha : (released u).gpr .eax = u.gpr .eax := released_gpr (by decide)
    revert hr
    cases sigI P (layOf P s) s.mem i with
    | some rs => exact fun ⟨h₁, h₂⟩ => ⟨by rw [BitVec.setWidth_append_eq_right, ha]; exact h₁, by rw [e₂]; exact h₂⟩
    | none => exact fun ⟨h₁, h₂⟩ => ⟨by rw [BitVec.setWidth_append_eq_right, ha]; exact h₁, h₂⟩

end VG.Proof.Ecdsa.Rfc6979.X86
