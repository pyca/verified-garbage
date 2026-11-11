module

public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtPinsA
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtMid2
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Flat
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA private-key operation on RISC-V: the registers at the later cuts

After `X`'s checks: the cuts after each block that loads a word of the header
(`loadIn`'s, the primes' working spaces', `reduceIn`'s count, the exponents',
`widen`'s, `recombineP`'s and the output's), with the registers
there from the initial state (`pins*`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64 (Scr add_ofNat_zero At pins_at_list)
open VG.Proof.Bignum.RISCV64.Pre (Pins)
open VG.Proof.Bignum (slot)
open VG.Impl.Bignum.RISCV64.PublicChecked (output)

variable {pc : Bool}

/-- A cut's index in `crtF pc`. -/
abbrev ix (pc : Bool) (a b : Nat) : Nat := if pc then b else a

/-- With `pc`, the cached values (`R2F`) and the header's word of their address. -/
theorem c0_r2 {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ s : State} (h : C0 pc d s₀)
    (hhd : pc = true → Mont.word s.mem (cS s₀) oR2 = s₀.gpr .s1) :
    pc = true → R2F s₀ ∧ Mont.word s.mem (cS s₀) oR2 = s₀.gpr .s1 := fun hp => by
  subst hp; exact ⟨r2F_of h.1, hhd rfl⟩

/-- The front, `loadX` and `checks`, then `c`. -/
abbrev NA (pc : Bool) (c : Prog isa) : Prog isa :=
  .seq (.block (Crt.save ++ argsG pc ++ setupX)) (.seq loadX (.seq checks c))

theorem na_ok {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ : State} {c : Prog isa}
    {Q : State → Prop} (h : C0 pc d s₀)
    (hc : ∀ s t, PF s₀ → Front s₀ s → (pc = true → Mont.word s.mem (cS s₀) oR2 = s₀.gpr .s1) → XS s₀ s t →
      t.gpr .a7 = Mont.off (cS s₀) (slot (cwX s₀) 0) →
      t.gpr .ra = Mont.off (cS s₀) (slot (cwX s₀) 0) → t.gpr .s5 = BitVec.ofNat 64 (8 * (cwX s₀ + 2)) →
      t.gpr .t0 = BitVec.ofNat 64 (cwX s₀) → WP isa c t Q) :
    WP isa (NA pc c) s₀ Q :=
  WP.seq (WP.mono (front_okG (pc := pc) s₀ (preG_core h.1)) fun s ⟨F, hd⟩ => stA_ok h.pf F fun t X a7 ra s5 t0 =>
    hc s t h.pf F hd X a7 ra s5 t0)

theorem pins98 : Pins (At (C0 pc) (crtF pc) 98) (rsX ++ ([.s7, .s8] : List Reg)) := by
  refine pins_at_list (fun s₀ => valsX s₀ ++ [Mont.off (s₀.gpr .a4) 0, BitVec.ofNat 64 (ck s₀)])
    (fun _ s₀ h => WP.of_flat (c := NA pc (LD oIn oNLen)) (by cases pc <;> rfl)
      (na_ok h fun s t hP F _ X a7 ra s5 t0 => ?_))
    fun _ _ _ h h' => let E := data_vals h h'; ldv_eq h h' E.2.2.2.2.2.2.1 E.2.1
  have room := hP.room
  refine WP.mono (ld2_ok (A := s₀.gpr .a4) (L := ck s₀) (X.scr F) (by unfold slot at room; omega_arith) X.s6
    (by decide) (by decide) (by rw [X.hdr hP (by unfold oIn oMask; omega_arith)]; exact F.hIn)
    (by rw [X.hdr hP (by unfold oNLen oMask; omega_arith)]; exact F.hNL)) fun u ⟨⟨a7', a8, _⟩, k⟩ => ?_
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, a7', a8, k.gpr (r := .a7) (by decide),
    k.gpr (r := .ra) (by decide), k.gpr (r := .s5) (by decide), k.gpr (r := .s11) (by decide),
    k.gpr (r := .t0) (by decide), k.gpr (r := .s6) (by decide), a7, ra, s5, X.s11, t0, X.s6]

/-- A prime's working space's registers. -/
abbrev rsP : List Reg := [.a7, .ra, .s5, .t0, .t2, .s6, .s11]

abbrev valsP (s₀ : State) (o l : Nat) : List (BitVec 64) :=
  [Mont.off (Mont.off (cS s₀) o) (slot (wordsOf l) 0), Mont.off (Mont.off (cS s₀) o) (slot (wordsOf l) 0),
    BitVec.ofNat 64 (8 * (wordsOf l + 2)), BitVec.ofNat 64 (wordsOf l), BitVec.ofNat 64 (wordsOf l), cS s₀,
    BitVec.ofNat 64 (8 * (cwX s₀ + 2))]

theorem valsP_map {s₀ s t : State} {o l : Nat} (X : XS s₀ s t) (R : PR s₀ o l t)
    (h2 : t.gpr .t2 = BitVec.ofNat 64 (wordsOf l)) : rsP.map t.gpr = valsP s₀ o l := by
  simp only [List.map_cons, List.map_nil, R.a7, R.ra, R.s5, R.t0, h2, X.s6, X.s11]

/-- With `pc`, `t6` (the cached `R²`'s address) in place of `t2`. -/
abbrev rsPG (pc : Bool) : List Reg := if pc then [.a7, .ra, .s5, .t0, .s6, .s11, .t6] else rsP

abbrev valsPG (pc : Bool) (s₀ : State) (o l : Nat) (c : Addr) : List (BitVec 64) :=
  if pc then [Mont.off (Mont.off (cS s₀) o) (slot (wordsOf l) 0), Mont.off (Mont.off (cS s₀) o) (slot (wordsOf l) 0),
    BitVec.ofNat 64 (8 * (wordsOf l + 2)), BitVec.ofNat 64 (wordsOf l), cS s₀,
    BitVec.ofNat 64 (8 * (cwX s₀ + 2)), c] else valsP s₀ o l

theorem valsPG_map {s₀ s t : State} {o l : Nat} {c : Addr} (X : XS s₀ s t) (R : PR s₀ o l t)
    (h6 : pc = true → t.gpr .t6 = c) (h2 : pc = false → t.gpr .t2 = BitVec.ofNat 64 (wordsOf l)) :
    (rsPG pc).map t.gpr = valsPG pc s₀ o l c := by
  cases pc
  · exact valsP_map X R (h2 rfl)
  · simp only [rsPG, valsPG, ↓reduceIte, List.map_cons, List.map_nil, R.a7, R.ra, R.s5, R.t0, X.s6, X.s11, h6 rfl]

theorem pins106 : Pins (At (C0 pc) (crtF pc) 106) (rsPG pc) := by
  refine pins_at_list (fun s₀ => valsPG pc s₀ (oPa s₀) (cpL s₀) (s₀.gpr .s1))
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NA pc (.seq loadIn (.seq (.block (setupP oBP oPLen ++ r2Ptr pc false))
      (.block [])))) (by cases pc <;> rfl) (na_ok h fun s t hP F hd X a7 ra s5 t0 => ?_))) fun _ _ _ h h' => ?_
  · refine stB_ok hP F X a7 ra s5 t0 fun u X' _ _ _ _ _ => stCG_ok (q := false) hP F X' (by decide) (by decide)
      F.hBP F.hPL hP.p1 (by have := hP.k1024; have := hP.pk; omega_arith) fun v Xv R c6 h2 _ =>
      wp_nil (valsPG_map Xv R (fun hp => by
        rw [c6 hp, hd hp]; simp only [Bool.false_eq_true, ↓reduceIte, BitVec.add_zero]) h2)
  · obtain ⟨eS, ek, ep, -⟩ := data_vals h h'
    have E := two_data h h'
    cases pc
    · simp only [valsPG, valsP, oPa, cwX, eS, ek, ep, Bool.false_eq_true, ↓reduceIte]
    · simp only [valsPG, oPa, cwX, eS, ek, ep, E.s1 rfl, ↓reduceIte]

/-- The registers at a prime's chunks. -/
abbrev rsC : List Reg := [.a7, .ra, .s5, .t0, .s6, .s11, .s9, .s10]

abbrev valsC (s₀ : State) (o l : Nat) : List (BitVec 64) :=
  [Mont.off (Mont.off (cS s₀) o) (slot (wordsOf l) 0), Mont.off (Mont.off (cS s₀) o) (slot (wordsOf l) 0),
    BitVec.ofNat 64 (8 * (wordsOf l + 2)), BitVec.ofNat 64 (wordsOf l), cS s₀, BitVec.ofNat 64 (8 * (cwX s₀ + 2)),
    Mont.off (cS s₀) (slot (cwX s₀) 6 + 8 * (wordsOf l * 0)),
    BitVec.ofNat 64 ((ck s₀ + 7) / 8) - BitVec.ofNat 64 (wordsOf l * 0)]

/-- The registers at a prime's exponent. -/
abbrev valsE (s₀ : State) (o l : Nat) (D : Addr) : List (BitVec 64) :=
  [Mont.off (Mont.off (cS s₀) o) (slot (wordsOf l) 0), Mont.off (Mont.off (cS s₀) o) (slot (wordsOf l) 0),
    BitVec.ofNat 64 (8 * (wordsOf l + 2)), BitVec.ofNat 64 (wordsOf l), cS s₀, BitVec.ofNat 64 (8 * (cwX s₀ + 2)),
    Mont.off D 0, BitVec.ofNat 64 l]

/-- `loadIn` and `p`'s working space, then `c`. -/
abbrev NP0 (pc : Bool) (c : Prog isa) : Prog isa :=
  NA pc (.seq loadIn (.seq (.block (setupP oBP oPLen ++ r2Ptr pc false)) c))

theorem np0_ok {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ : State} {c : Prog isa}
    {Q : State → Prop} (h : C0 pc d s₀)
    (hc : ∀ s t, PF s₀ → Front s₀ s → (pc = true → Mont.word s.mem (cS s₀) oR2 = s₀.gpr .s1) → XS s₀ s t →
      wordsVal t.mem (cS s₀) (slot (cwX s₀) 6) (cwX s₀) = vC s₀ → PR s₀ (oPa s₀) (cpL s₀) t →
      (pc = true → t.gpr .t6 = Mont.word s.mem (cS s₀) oR2 + BitVec.ofNat 64 (if false then 8 * cwP s₀ else 0)) →
      WP isa c t Q) :
    WP isa (NP0 pc c) s₀ Q :=
  na_ok h fun s _ hP F hd X a7 ra s5 t0 => stB_ok hP F X a7 ra s5 t0 fun _ X' v6 _ _ _ _ =>
    stCG_ok (q := false) hP F X' (by decide) (by decide) F.hBP F.hPL hP.p1
      (by have := hP.k1024; have := hP.pk; omega_arith) fun u Xu R c4 _ m => hc s u hP F hd Xu (by rw [m]; exact v6) R c4

theorem pins134 : Pins (At (C0 pc) (crtF pc) (ix pc 134 129)) rsC := by
  refine pins_at_list (fun s₀ => valsC s₀ (oPa s₀) (cpL s₀))
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NP0 pc (Win.powerPG pc 4 (Win.reduceInP (.block []))))
      (by cases pc <;> rfl) (np0_ok h fun s t hP F hd X v6 R c4 => ?_))) fun _ _ _ h h' => ?_
  · obtain ⟨mP1, mPo, -, -, mPb, -, -, -⟩ := masked_facts hP
    have room := hP.room
    refine WP.mono (stD134G_ok hP F X v6 R (Nat.le_refl _) (by have : oPa s₀ = slot (cwX s₀) 8 := rfl; omega_arith)
      (slot_al _ _) (by decide) X.x4 mPb mP1 mPo hP.pk (r2c_p hP F (c0_r2 h hd) X c4))
      fun u ⟨R', h6, h11, h9, h10⟩ => ?_
    simp only [List.map_cons, List.map_nil, R'.a7, R'.ra, R'.s5, R'.t0, h6, h11, h9, h10]
  · obtain ⟨eS, ek, ep, -⟩ := data_vals h h'
    simp only [valsC, oPa, cwX, eS, ek, ep]

theorem pins136 : Pins (At (C0 pc) (crtF pc) (ix pc 136 131)) rsC := by
  refine pins_at_list (fun s₀ => valsE s₀ (oPa s₀) (cpL s₀) (stackArg s₀ 2))
    (fun _ s₀ h => WP.of_flat (c := NP0 pc (Win.powerPG pc 4 (.seq Crt.reduceIn
      (.block [.load .d .s9 .s6 oDP, .load .d .s10 .s6 oPLen])))) (by cases pc <;> rfl)
      (np0_ok h fun s t hP F hd X v6 R c4 => ?_)) fun _ _ _ h h' => ?_
  · obtain ⟨mP1, mPo, -, -, mPb, -, -, -⟩ := masked_facts hP
    have room := hP.room
    refine WP.mono (stD136G_ok (oD := oDP) (oLen := oPLen) hP F X v6 R (Nat.le_refl _)
      (by have : oPa s₀ = slot (cwX s₀) 8 := rfl; omega_arith) (slot_al _ _) (by decide) X.x4 mPb mP1 mPo hP.pk
      (by decide) (by decide) F.hDP F.hPL (r2c_p hP F (c0_r2 h hd) X c4)) fun u ⟨R', h6, h11, h9, h10⟩ => ?_
    simp only [List.map_cons, List.map_nil, R'.a7, R'.ra, R'.s5, R'.t0, h6, h11, h9, h10]
  · obtain ⟨eS, ek, ep, -, -, -, -, -, -, e2, -⟩ := data_vals h h'
    simp only [valsE, oPa, cwX, eS, ek, ep, e2]

/-- `m₁`, then `q`'s working space, then `c`. -/
abbrev NQ0 (pc : Bool) (c : Prog isa) : Prog isa :=
  NP0 pc (.seq (powerG pc 4 oDP oPLen) (.seq (.block (setupP oBQ oQLen ++ r2Ptr pc true)) c))

theorem nq0_ok {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ : State} {c : Prog isa}
    {Q : State → Prop} (h : C0 pc d s₀)
    (hc : ∀ s t, PF s₀ → Front s₀ s → (pc = true → Mont.word s.mem (cS s₀) oR2 = s₀.gpr .s1) → XS s₀ s t →
      wordsVal t.mem (cS s₀) (slot (cwX s₀) 6) (cwX s₀) = vC s₀ → PR s₀ (oQa s₀) (cqL s₀) t →
      (pc = true → t.gpr .t6 = Mont.word s.mem (cS s₀) oR2 + BitVec.ofNat 64 (if true then 8 * cwP s₀ else 0)) →
      (pc = false → t.gpr .t2 = BitVec.ofNat 64 (wordsOf (cqL s₀))) → WP isa c t Q) :
    WP isa (NQ0 pc c) s₀ Q := by
  refine np0_ok h fun s t hP F hd X v6 R c4 => ?_
  obtain ⟨mP1, mPo, -, -, mPb, -, -, -⟩ := masked_facts hP
  have room := hP.room
  refine WP.seq (WP.mono (stDG_ok (xj := 4) (D := stackArg s₀ 2) hP F X v6 R (Nat.le_refl _)
    (by have : oPa s₀ = slot (cwX s₀) 8 := rfl; omega_arith) (slot_al _ _) (by decide) X.x4 mPb mP1 mPo hP.p1 hP.pk
    (by decide) (by decide) F.hDP F.hPL hP.rDP hP.sDP (r2c_p hP F (c0_r2 h hd) X c4)) fun t₅ ⟨X5, v6', _⟩ => ?_)
  exact stCG_ok (q := true) hP F X5 (by decide) (by decide) F.hBQ F.hQL hP.q1
    (by have := hP.k1024; have := hP.qk; omega_arith)
    fun u Xu R' c6 h2 m => hc s u hP F hd Xu (by rw [m]; exact v6') R' c6 h2

theorem pins177 : Pins (At (C0 pc) (crtF pc) (ix pc 177 172)) (rsPG pc) := by
  refine pins_at_list (fun s₀ => valsPG pc s₀ (oQa s₀) (cqL s₀) (s₀.gpr .s1 + BitVec.ofNat 64 (8 * cwP s₀)))
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NQ0 pc (.block [])) (by cases pc <;> decide +kernel)
      (nq0_ok h fun s t hP F hd X _ R c6 h2 => wp_nil (valsPG_map X R (fun hp => by
        rw [c6 hp, hd hp]; simp only [↓reduceIte]) h2)))) fun _ _ _ h h' => ?_
  obtain ⟨eS, ek, ep, eq, -⟩ := data_vals h h'
  have E := two_data h h'
  cases pc
  · simp only [valsPG, valsP, oQa, cwP, cwX, eS, ek, ep, eq, Bool.false_eq_true, ↓reduceIte]
  · simp only [valsPG, oQa, cwP, cwX, eS, ek, ep, eq, E.s1 rfl, ↓reduceIte]

theorem oQa_al (s₀ : State) : oQa s₀ % 8 = 0 := by
  have := slot_al (cwX s₀) 8; have := slot_al (cwP s₀) 24; show (slot (cwX s₀) 8 + slot (cwP s₀) 24) % 8 = 0
  omega_arith

theorem pins205 : Pins (At (C0 pc) (crtF pc) (ix pc 205 195)) rsC := by
  refine pins_at_list (fun s₀ => valsC s₀ (oQa s₀) (cqL s₀))
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NQ0 pc (Win.powerPG pc 5 (Win.reduceInP (.block []))))
      (by cases pc <;> decide +kernel) (nq0_ok h fun s t hP F hd X v6 R c6 _ => ?_))) fun _ _ _ h h' => ?_
  · obtain ⟨-, -, mQ1, mQo, -, mQb, -, -⟩ := masked_facts hP
    have room := hP.room
    refine WP.mono (stD134G_ok hP F X v6 R (by show slot (cwX s₀) 8 ≤ slot (cwX s₀) 8 + slot (cwP s₀) 24; omega_arith)
      (by have : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl; omega_arith)
      (oQa_al _) (by decide) X.x5 mQb mQ1 mQo hP.qk (r2c_q hP F (c0_r2 h hd) X c6)) fun u ⟨R', h6, h11, h9, h10⟩ => ?_
    simp only [List.map_cons, List.map_nil, R'.a7, R'.ra, R'.s5, R'.t0, h6, h11, h9, h10]
  · obtain ⟨eS, ek, ep, eq, -⟩ := data_vals h h'
    simp only [valsC, oQa, cwP, cwX, eS, ek, ep, eq]

theorem pins207 : Pins (At (C0 pc) (crtF pc) (ix pc 207 197)) rsC := by
  refine pins_at_list (fun s₀ => valsE s₀ (oQa s₀) (cqL s₀) (stackArg s₀ 4))
    (fun _ s₀ h => WP.of_flat (c := NQ0 pc (Win.powerPG pc 5 (.seq Crt.reduceIn
      (.block [.load .d .s9 .s6 oDQ, .load .d .s10 .s6 oQLen])))) (by cases pc <;> decide +kernel)
      (nq0_ok h fun s t hP F hd X v6 R c6 _ => ?_)) fun _ _ _ h h' => ?_
  · obtain ⟨-, -, mQ1, mQo, -, mQb, -, -⟩ := masked_facts hP
    have room := hP.room
    refine WP.mono (stD136G_ok (oD := oDQ) (oLen := oQLen) hP F X v6 R
      (by show slot (cwX s₀) 8 ≤ slot (cwX s₀) 8 + slot (cwP s₀) 24; omega_arith)
      (by have : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl; omega_arith) (oQa_al _) (by decide) X.x5 mQb
      mQ1 mQo hP.qk (by decide) (by decide) F.hDQ F.hQL (r2c_q hP F (c0_r2 h hd) X c6))
      fun u ⟨R', h6, h11, h9, h10⟩ => ?_
    simp only [List.map_cons, List.map_nil, R'.a7, R'.ra, R'.s5, R'.t0, h6, h11, h9, h10]
  · obtain ⟨eS, ek, ep, eq, -, -, -, -, -, -, e4, -⟩ := data_vals h h'
    simp only [valsE, oQa, cwP, cwX, eS, ek, ep, eq, e4]

/-- The front and the powers, then `c`. -/
abbrev NM (pc : Bool) (c : Prog isa) : Prog isa := .seq (.block (Crt.save ++ argsG pc ++ setupX)) (mid1CG pc c)

theorem nm_ok {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ : State} {c : Prog isa}
    {Q : State → Prop} (h : C0 pc d s₀) (hc : ∀ s t, PF s₀ → Front s₀ s → M1 s₀ s t → WP isa c t Q) :
    WP isa (NM pc c) s₀ Q :=
  WP.seq (WP.mono (front_okG (pc := pc) s₀ (preG_core h.1)) fun s ⟨F, hd⟩ =>
    mid1G_ok h.pf F (c0_r2 h hd) fun t M => hc s t h.pf F M)

/-- `m₂` widened into `X`'s array 6, `p`'s working space and the start of `recombineP`, then `c`. -/
abbrev NR (pc : Bool) (c : Prog isa) : Prog isa :=
  NM pc (.seq (widen oBQ oQLen 6) (.seq (.block (setupP oBP oPLen)) c))

theorem pins254 : Pins (At (C0 pc) (crtF pc) (ix pc 254 244)) rsP := by
  refine pins_at_list (fun s₀ => valsP s₀ (oPa s₀) (cpL s₀))
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NR pc (.block [])) (by cases pc <;> decide +kernel)
      (nm_ok h fun s t hP F M => m2A_ok hP F M fun u Y h2 => wp_nil ?_)))
    fun _ _ _ h h' => ?_
  · simp only [List.map_cons, List.map_nil, Y.R.a7, Y.R.ra, Y.R.s5, Y.R.t0, h2, Y.s6, Y.s11]
  · obtain ⟨eS, ek, ep, -⟩ := data_vals h h'
    simp only [valsP, oPa, cwX, eS, ek, ep]

theorem pins275 : Pins (At (C0 pc) (crtF pc) (ix pc 275 265)) rsC := by
  refine pins_at_list (fun s₀ => valsC s₀ (oPa s₀) (cpL s₀))
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NR pc (recPA (Win.reduceInP (.block [])))) (by cases pc <;> decide +kernel)
      (nm_ok h fun s t hP F M => m2A_ok hP F M fun u Y _ => ?_))) fun _ _ _ h h' => ?_
  · have hn := hP.nw
    have room := hP.room
    have k64 := hP.k64; have k1024 := hP.k1024; have pk := hP.pk
    have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
    have eX6 := e (cwX s₀) 6; have eX8 := e (cwX s₀) 8; have eP24 := e (cwP s₀) 24
    have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
    have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
    have dP : cwP s₀ = wordsOf (cpL s₀) := rfl
    have room' : oPa s₀ + slot (cwP s₀) 24 + slot (cwQ s₀) 24 ≤ cZ s₀ := room
    have hwP2 : 2 ≤ cwP s₀ := two_le_wordsOf
    have hwPK : cwP s₀ ≤ (ck s₀ + 7) / 8 := wordsOf_le_of (Nat.le_of_lt pk) (by omega_arith)
    have hZ256 : 256 ≤ cZ s₀ := by omega_arith
    obtain ⟨mP1, mPo, -, -, -, -, -, -⟩ := masked_facts hP
    have hS2 : Scr u (cS s₀) (cZ s₀) := F.scr.congr Y.wr
    have hK : 1 ≤ (ck s₀ + 7) / 8 := by omega_arith
    have n2 := Win.nChunks_mul_lt (K := (ck s₀ + 7) / 8) (w := cwP s₀) (by omega_arith) hK
    rw [Nat.mul_comm] at n2
    refine WP.mono (recPC_ok (Pv := mP s₀) (k := ck s₀)
      (Scr.sub hS2 (show oPa s₀ + slot (cwP s₀) 24 ≤ cZ s₀ by omega_arith) (slot_al _ _) (by omega_arith))
      (Scr.le hS2 (show slot (cwX s₀) 8 ≤ cZ s₀ by omega_arith))
      (sepXB (Nat.le_refl _) (by omega_arith) (by omega_arith)) (Nat.le_refl _) (Nat.le_refl _) hwP2
      (by omega_arith) Y.R.a7 Y.R.ra Y.R.s5 Y.R.t0 Y.s6 Y.s11
      ((hdr_mid Y.fr hZ256 (by unfold oNLen oMask; omega_arith)).trans F.hNL) (by omega_arith) (by omega_arith)
      (by omega_arith) Y.p0 mP1 mPo Y.p1) fun v ⟨a7, ra, s5, t0, s6, s11, s9, s10⟩ => ?_
    simp only [List.map_cons, List.map_nil, a7, ra, s5, t0, s6, s11, s9, s10]
  · obtain ⟨eS, ek, ep, -⟩ := data_vals h h'
    simp only [valsC, oPa, cwX, eS, ek, ep]

/-- `widen`'s first block. -/
abbrev WD1 (oB oLen xj : Nat) : List Instr :=
  setupP oB oLen ++ PublicChecked.base .s9 4 ++ [.addi .s8 .t0 0] ++ xb .t3 xj ++ Crt.wX

abbrev rsW : List Reg := [.a7, .ra, .s5, .s11, .t0, .s6, .s9, .s8, .t3]

abbrev valsW (s₀ : State) (o l xj : Nat) : List (BitVec 64) :=
  [Mont.off (Mont.off (cS s₀) o) (slot (wordsOf l) 0), Mont.off (Mont.off (cS s₀) o) (slot (wordsOf l) 0),
    BitVec.ofNat 64 (8 * (wordsOf l + 2)), BitVec.ofNat 64 (8 * (cwX s₀ + 2)), BitVec.ofNat 64 (cwX s₀), cS s₀,
    Mont.off (Mont.off (cS s₀) o) (slot (wordsOf l) 4), BitVec.ofNat 64 (wordsOf l),
    Mont.off (cS s₀) (slot (cwX s₀) xj)]

/-- `widen`'s first block, from a state whose header is the front's. -/
theorem wd1_vals {s₀ u : State} {oB oLen o l xj : Nat} (hP : PF s₀)
    (hs : Scr u (cS s₀) (cZ s₀)) (h6 : u.gpr .s6 = cS s₀) (h11 : u.gpr .s11 = BitVec.ofNat 64 (8 * (cwX s₀ + 2)))
    (hoB : oB + 8 ≤ 256 ∧ oB % 8 = 0) (hoL : oLen + 8 ≤ 256 ∧ oLen % 8 = 0)
    (hB : Mont.word u.mem (cS s₀) oB = Mont.off (cS s₀) o) (hL : Mont.word u.mem (cS s₀) oLen = BitVec.ofNat 64 l)
    (hl1 : 1 ≤ l) (hl : l ≤ 1024) :
    WP isa (.block (WD1 oB oLen xj)) u fun v => rsW.map v.gpr = valsW s₀ o l xj := by
  have room := hP.room; have k1024 := hP.k1024
  have hZ : 256 ≤ cZ s₀ := by unfold slot at room; omega_arith
  refine WP.mono (wd1_ok (xj := xj) hs h6 h11 (by omega_arith) hoB.2 (by omega_arith) (by omega_arith) hoL.2
    (by omega_arith) hB hL hl1 hl (by have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl; omega_arith))
    fun v ⟨⟨a7, ra, a5, a9, a8, a3, a0⟩, k⟩ => ?_
  simp only [List.map_cons, List.map_nil, a7, ra, a5, a9, a8, a3, a0, k.gpr (r := .s6) (by decide),
    k.gpr (r := .s11) (by decide), h6, h11]

theorem valsW_eq {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ s₀' : State} (h : C0 pc d s₀)
    (h' : C0 pc d s₀') {o o' l l' : Nat} (xj : Nat) (ho : o = o') (hl : l = l') :
    valsW s₀ o l xj = valsW s₀' o' l' xj := by
  obtain ⟨eS, ek, -⟩ := data_vals h h'
  simp only [valsW, cwX, eS, ek, ho, hl]

theorem pins248 : Pins (At (C0 pc) (crtF pc) (ix pc 248 238)) rsW := by
  refine pins_at_list (fun s₀ => valsW s₀ (oQa s₀) (cqL s₀) 6)
    (fun _ s₀ h => WP.of_flat (c := NM pc (.block (WD1 oBQ oQLen 6))) (by cases pc <;> decide +kernel)
      (nm_ok h fun s t hP F M => ?_)) fun _ _ _ h h' => ?_
  · have room := hP.room
    have hZ : 256 ≤ cZ s₀ := by unfold slot at room; omega_arith
    exact wd1_vals hP (F.scr.congr M.keep.2.2) M.s6 M.s11 (by decide) (by decide)
      ((hdr_mid M.fr hZ (by unfold oBQ oMask; omega_arith)).trans F.hBQ)
      ((hdr_mid M.fr hZ (by unfold oQLen oMask; omega_arith)).trans F.hQL) hP.q1
      (by have := hP.k1024; have := hP.qk; omega_arith)
  · obtain ⟨eS, ek, ep, eq, -⟩ := data_vals h h'
    exact valsW_eq h h' 6 (by simp only [oQa, cwP, cwX, ek, ep]) eq

theorem pins305 : Pins (At (C0 pc) (crtF pc) (ix pc 305 295)) rsW := by
  refine pins_at_list (fun s₀ => valsW s₀ (oPa s₀) (cpL s₀) 7)
    (fun _ s₀ h => WP.of_flat (c := NR pc (.seq recombineP
      (.block (WD1 oBP oPLen 7)))) (by cases pc <;> decide +kernel)
      (nm_ok h fun s t hP F M => m2A_ok hP F M fun u Y _ => m2B_ok hP F Y fun v Y3 => ?_))
    fun _ _ _ h h' => ?_
  · have room := hP.room
    have hZ : 256 ≤ cZ s₀ := by unfold slot at room; omega_arith
    exact wd1_vals hP (F.scr.congr Y3.wr) Y3.s6 Y3.s11 (by decide) (by decide)
      ((hdr_mid Y3.fr hZ (by unfold oBP oMask; omega_arith)).trans F.hBP)
      ((hdr_mid Y3.fr hZ (by unfold oPLen oMask; omega_arith)).trans F.hPL) hP.p1
      (by have := hP.k1024; have := hP.pk; omega_arith)
  · obtain ⟨eS, ek, ep, -⟩ := data_vals h h'
    exact valsW_eq h h' 7 (by simp only [oPa, cwX, ek]) ep

theorem pins311 : Pins (At (C0 pc) (crtF pc) (ix pc 311 301)) rsW := by
  refine pins_at_list (fun s₀ => valsW s₀ (oQa s₀) (cqL s₀) 6)
    (fun _ s₀ h => WP.of_flat (c := NR pc (.seq recombineP
      (.seq (widen oBP oPLen 7) (.block (WD1 oBQ oQLen 6))))) (by cases pc <;> decide +kernel)
      (nm_ok h fun s t hP F M => m2A_ok hP F M fun u Y _ => m2B_ok hP F Y fun v Y3 => ?_))
    fun _ _ _ h h' => ?_
  · have room := hP.room; have k1024 := hP.k1024; have pk := hP.pk; have qk := hP.qk
    have hn := hP.nw
    have hZ : 256 ≤ cZ s₀ := by unfold slot at room; omega_arith
    have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
    have eX7 := e (cwX s₀) 7; have eX8 := e (cwX s₀) 8; have eP8 := e (wordsOf (cpL s₀)) 8
    have eP24 := e (wordsOf (cpL s₀)) 24
    have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
    have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
    have hwPK : wordsOf (cpL s₀) ≤ (ck s₀ + 7) / 8 := wordsOf_le_of (Nat.le_of_lt pk) (by have := hP.k64; omega_arith)
    have hs := F.scr.congr Y3.wr
    refine WP.seq (WP.mono (widen_ok (xj := 7) (Scr.le hs (show slot (cwX s₀) 8 ≤ cZ s₀ by omega_arith))
      (Scr.sub hs (show oPa s₀ + slot (wordsOf (cpL s₀)) 24 ≤ cZ s₀ by omega_arith) (slot_al _ _) (by omega_arith))
      (sepBX (Nat.le_refl _) (by omega_arith) (by omega_arith)) Y3.s6 Y3.s11 (by unfold oBP; omega_arith) (by decide)
      (by decide) (by unfold oPLen; omega_arith) (by decide) (by decide)
      ((hdr_mid Y3.fr hZ (by unfold oBP oMask; omega_arith)).trans F.hBP)
      ((hdr_mid Y3.fr hZ (by unfold oPLen oMask; omega_arith)).trans F.hPL) hP.p1 (by omega_arith) (by decide)
      (Nat.le_refl _) (by omega_arith) (by omega_arith) (by omega_arith)) fun w ⟨⟨_, O⟩, k⟩ => ?_)
    have hd : ∀ d, d + 8 ≤ 256 → Mont.word w.mem (cS s₀) d = Mont.word v.mem (cS s₀) d := fun d hd' =>
      Mont.Outside.word O (Or.inl (by omega_arith)) (by omega_arith)
    exact wd1_vals hP (hs.congr k.2.2) ((k.gpr (by decide)).trans Y3.s6) ((k.gpr (by decide)).trans Y3.s11)
      (by decide) (by decide)
      ((hd _ (by unfold oBQ; omega_arith)).trans ((hdr_mid Y3.fr hZ (by unfold oBQ oMask; omega_arith)).trans F.hBQ))
      ((hd _ (by unfold oQLen; omega_arith)).trans ((hdr_mid Y3.fr hZ (by unfold oQLen oMask; omega_arith)).trans F.hQL))
      hP.q1 (by omega_arith)
  · obtain ⟨eS, ek, ep, eq, -⟩ := data_vals h h'
    exact valsW_eq h h' 6 (by simp only [oQa, cwP, cwX, ek, ep]) eq

theorem pins330 : Pins (At (C0 pc) (crtF pc) (ix pc 330 320)) [.a7, .s5, .s6, .s10, .s11] := by
  refine pins_at_list (fun s₀ => [Mont.off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (8 * (cwX s₀ + 2)), cS s₀,
      Mont.off (s₀.gpr .a0) 0, BitVec.ofNat 64 (ck s₀)])
    (fun _ s₀ h => WP.of_flat (c := NR pc (.seq recombineP
      (.seq recombineX (.block finBlk)))) (by cases pc <;> decide +kernel)
      (nm_ok h fun s t hP F M => m2A_ok hP F M fun u Y _ => m2B_ok hP F Y fun v Y3 => m2C_ok hP F Y3 fun w Y4 => ?_))
    fun _ _ _ h h' => ?_
  · have room := hP.room
    have hZ : 256 ≤ cZ s₀ := by unfold slot at room; omega_arith
    refine WP.mono (fin1_ok (F.scr.congr Y4.wr) Y4.s6 Y4.s11
      ((hdr_mid Y4.fr hZ (by unfold oOut oMask; omega_arith)).trans F.hOut)
      ((hdr_mid Y4.fr hZ (by unfold oNLen oMask; omega_arith)).trans F.hNL) (by omega_arith))
      fun x ⟨⟨a7, a5, a10, a11, a6⟩, _⟩ => ?_
    simp only [List.map_cons, List.map_nil, a7, a5, a10, a11, a6]
  · obtain ⟨eS, ek, -, -, e0, -⟩ := data_vals h h'
    simp only [cwX, eS, ek, e0]

end VG.Proof.Bignum.RISCV64.Crt
