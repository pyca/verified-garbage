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
`exportM2`'s, `recombineP`'s, `widen`'s and the output's), with the registers
there from the initial state (`pins*`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64 (Scr add_ofNat_zero At pins_at_list)
open VG.Proof.Bignum.RISCV64.Pre (Pins)
open VG.Proof.Bignum (slot)
open VG.Impl.Bignum.RISCV64.PublicChecked (output)

/-- The front, `loadX` and `checks`, then `c`. -/
abbrev NA (c : Prog isa) : Prog isa :=
  .seq (.block (Crt.save ++ Crt.args ++ setupX)) (.seq loadX (.seq checks c))

theorem na_ok {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ : State} {c : Prog isa}
    {Q : State → Prop} (h : C0 d s₀)
    (hc : ∀ s t, PF s₀ → Front s₀ s → XS s₀ s t → t.gpr .a7 = Mont.off (cS s₀) (slot (cwX s₀) 0) →
      t.gpr .ra = Mont.off (cS s₀) (slot (cwX s₀) 0) → t.gpr .s5 = BitVec.ofNat 64 (8 * (cwX s₀ + 2)) →
      t.gpr .t0 = BitVec.ofNat 64 (cwX s₀) → WP isa c t Q) :
    WP isa (NA c) s₀ Q :=
  WP.seq (WP.mono (front_ok s₀ h.1) fun s F => stA_ok (pre_facts h.1) F fun t X a7 ra s5 t0 =>
    hc s t (pre_facts h.1) F X a7 ra s5 t0)

theorem pins98 : Pins (At C0 crtF 98) (rsX ++ ([.s7, .s8] : List Reg)) := by
  refine pins_at_list (fun s₀ => valsX s₀ ++ [Mont.off (s₀.gpr .a4) 0, BitVec.ofNat 64 (ck s₀)])
    (fun _ s₀ h => WP.of_flat (c := NA (LD oIn oNLen)) rfl (na_ok h fun s t hP F X a7 ra s5 t0 => ?_))
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

theorem pins106 : Pins (At C0 crtF 106) rsP := by
  refine pins_at_list (fun s₀ => valsP s₀ (oPa s₀) (cpL s₀))
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NA (.seq loadIn (.seq (.block (setupP oBP oPLen)) (.block []))))
      rfl (na_ok h fun s t hP F X a7 ra s5 t0 => ?_))) fun _ _ _ h h' => ?_
  · refine stB_ok hP F X a7 ra s5 t0 fun u X' _ _ _ _ _ => stC_ok hP F X' (by decide) (by decide) F.hBP F.hPL hP.p1
      (by have := hP.k1024; have := hP.pk; omega_arith) fun v Xv R h2 _ => wp_nil (valsP_map Xv R h2)
  · obtain ⟨eS, ek, ep, -⟩ := data_vals h h'
    simp only [valsP, oPa, cwX, eS, ek, ep]

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
abbrev NP0 (c : Prog isa) : Prog isa := NA (.seq loadIn (.seq (.block (setupP oBP oPLen)) c))

theorem np0_ok {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ : State} {c : Prog isa}
    {Q : State → Prop} (h : C0 d s₀)
    (hc : ∀ s t, PF s₀ → Front s₀ s → XS s₀ s t → wordsVal t.mem (cS s₀) (slot (cwX s₀) 6) (cwX s₀) = vC s₀ →
      PR s₀ (oPa s₀) (cpL s₀) t → WP isa c t Q) :
    WP isa (NP0 c) s₀ Q :=
  na_ok h fun s _ hP F X a7 ra s5 t0 => stB_ok hP F X a7 ra s5 t0 fun _ X' v6 _ _ _ _ =>
    stC_ok hP F X' (by decide) (by decide) F.hBP F.hPL hP.p1 (by have := hP.k1024; have := hP.pk; omega_arith)
      fun u Xu R _ m => hc s u hP F Xu (by rw [m]; exact v6) R

theorem pins134 : Pins (At C0 crtF 134) rsC := by
  refine pins_at_list (fun s₀ => valsC s₀ (oPa s₀) (cpL s₀))
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NP0 (Win.powerP 4 (Win.reduceInP (.block [])))) rfl
      (np0_ok h fun s t hP F X v6 R => ?_))) fun _ _ _ h h' => ?_
  · obtain ⟨mP1, mPo, -, -, mPb, -, -, -⟩ := masked_facts hP
    have room := hP.room
    refine WP.mono (stD134_ok hP F X v6 R (Nat.le_refl _) (by have : oPa s₀ = slot (cwX s₀) 8 := rfl; omega_arith)
      (slot_al _ _) (by decide) X.x4 mPb mP1 mPo hP.pk) fun u ⟨R', h6, h11, h9, h10⟩ => ?_
    simp only [List.map_cons, List.map_nil, R'.a7, R'.ra, R'.s5, R'.t0, h6, h11, h9, h10]
  · obtain ⟨eS, ek, ep, -⟩ := data_vals h h'
    simp only [valsC, oPa, cwX, eS, ek, ep]

theorem pins136 : Pins (At C0 crtF 136) rsC := by
  refine pins_at_list (fun s₀ => valsE s₀ (oPa s₀) (cpL s₀) (stackArg s₀ 2))
    (fun _ s₀ h => WP.of_flat (c := NP0 (Win.powerP 4 (.seq Crt.reduceIn
      (.block [.load .d .s9 .s6 oDP, .load .d .s10 .s6 oPLen])))) rfl
      (np0_ok h fun s t hP F X v6 R => ?_)) fun _ _ _ h h' => ?_
  · obtain ⟨mP1, mPo, -, -, mPb, -, -, -⟩ := masked_facts hP
    have room := hP.room
    refine WP.mono (stD136_ok (oD := oDP) (oLen := oPLen) hP F X v6 R (Nat.le_refl _)
      (by have : oPa s₀ = slot (cwX s₀) 8 := rfl; omega_arith) (slot_al _ _) (by decide) X.x4 mPb mP1 mPo hP.pk
      (by decide) (by decide) F.hDP F.hPL) fun u ⟨R', h6, h11, h9, h10⟩ => ?_
    simp only [List.map_cons, List.map_nil, R'.a7, R'.ra, R'.s5, R'.t0, h6, h11, h9, h10]
  · obtain ⟨eS, ek, ep, -, -, -, -, -, -, e2, -⟩ := data_vals h h'
    simp only [valsE, oPa, cwX, eS, ek, ep, e2]

/-- `m₁`, then `q`'s working space, then `c`. -/
abbrev NQ0 (c : Prog isa) : Prog isa := NP0 (.seq (power 4 oDP oPLen) (.seq (.block (setupP oBQ oQLen)) c))

theorem nq0_ok {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ : State} {c : Prog isa}
    {Q : State → Prop} (h : C0 d s₀)
    (hc : ∀ s t, PF s₀ → Front s₀ s → XS s₀ s t → wordsVal t.mem (cS s₀) (slot (cwX s₀) 6) (cwX s₀) = vC s₀ →
      PR s₀ (oQa s₀) (cqL s₀) t → WP isa c t Q) :
    WP isa (NQ0 c) s₀ Q := by
  refine np0_ok h fun s t hP F X v6 R => ?_
  obtain ⟨mP1, mPo, -, -, mPb, -, -, -⟩ := masked_facts hP
  have room := hP.room
  refine WP.seq (WP.mono (stD_ok (xj := 4) (D := stackArg s₀ 2) hP F X v6 R (Nat.le_refl _)
    (by have : oPa s₀ = slot (cwX s₀) 8 := rfl; omega_arith) (slot_al _ _) (by decide) X.x4 mPb mP1 mPo hP.p1 hP.pk
    (by decide) (by decide) F.hDP F.hPL hP.rDP hP.sDP) fun t₅ ⟨X5, v6', _⟩ => ?_)
  exact stC_ok hP F X5 (by decide) (by decide) F.hBQ F.hQL hP.q1 (by have := hP.k1024; have := hP.qk; omega_arith)
    fun u Xu R' _ m => hc s u hP F Xu (by rw [m]; exact v6') R'

theorem pins177 : Pins (At C0 crtF 177) rsP := by
  refine pins_at_list (fun s₀ => valsP s₀ (oQa s₀) (cqL s₀))
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NP0 (.seq (power 4 oDP oPLen) (.seq (.block (setupP oBQ oQLen))
      (.block [])))) (by decide +kernel) (np0_ok h fun s t hP F X v6 R => ?_))) fun _ _ _ h h' => ?_
  · obtain ⟨mP1, mPo, -, -, mPb, -, -, -⟩ := masked_facts hP
    have room := hP.room
    refine WP.seq (WP.mono (stD_ok (xj := 4) (D := stackArg s₀ 2) hP F X v6 R (Nat.le_refl _)
      (by have : oPa s₀ = slot (cwX s₀) 8 := rfl; omega_arith) (slot_al _ _) (by decide) X.x4 mPb mP1 mPo hP.p1 hP.pk
      (by decide) (by decide) F.hDP F.hPL hP.rDP hP.sDP) fun t₅ ⟨X5, _⟩ => ?_)
    exact stC_ok hP F X5 (by decide) (by decide) F.hBQ F.hQL hP.q1 (by have := hP.k1024; have := hP.qk; omega_arith)
      fun u Xu R' h2 _ => wp_nil (valsP_map Xu R' h2)
  · obtain ⟨eS, ek, ep, eq, -⟩ := data_vals h h'
    simp only [valsP, oQa, cwP, cwX, eS, ek, ep, eq]

theorem oQa_al (s₀ : State) : oQa s₀ % 8 = 0 := by
  have := slot_al (cwX s₀) 8; have := slot_al (cwP s₀) 24; show (slot (cwX s₀) 8 + slot (cwP s₀) 24) % 8 = 0
  omega_arith

theorem pins205 : Pins (At C0 crtF 205) rsC := by
  refine pins_at_list (fun s₀ => valsC s₀ (oQa s₀) (cqL s₀))
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NQ0 (Win.powerP 5 (Win.reduceInP (.block [])))) (by decide +kernel)
      (nq0_ok h fun s t hP F X v6 R => ?_))) fun _ _ _ h h' => ?_
  · obtain ⟨-, -, mQ1, mQo, -, mQb, -, -⟩ := masked_facts hP
    have room := hP.room
    refine WP.mono (stD134_ok hP F X v6 R (by show slot (cwX s₀) 8 ≤ slot (cwX s₀) 8 + slot (cwP s₀) 24; omega_arith)
      (by have : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl; omega_arith)
      (oQa_al _) (by decide) X.x5 mQb mQ1 mQo hP.qk) fun u ⟨R', h6, h11, h9, h10⟩ => ?_
    simp only [List.map_cons, List.map_nil, R'.a7, R'.ra, R'.s5, R'.t0, h6, h11, h9, h10]
  · obtain ⟨eS, ek, ep, eq, -⟩ := data_vals h h'
    simp only [valsC, oQa, cwP, cwX, eS, ek, ep, eq]

theorem pins207 : Pins (At C0 crtF 207) rsC := by
  refine pins_at_list (fun s₀ => valsE s₀ (oQa s₀) (cqL s₀) (stackArg s₀ 4))
    (fun _ s₀ h => WP.of_flat (c := NQ0 (Win.powerP 5 (.seq Crt.reduceIn
      (.block [.load .d .s9 .s6 oDQ, .load .d .s10 .s6 oQLen])))) (by decide +kernel)
      (nq0_ok h fun s t hP F X v6 R => ?_)) fun _ _ _ h h' => ?_
  · obtain ⟨-, -, mQ1, mQo, -, mQb, -, -⟩ := masked_facts hP
    have room := hP.room
    refine WP.mono (stD136_ok (oD := oDQ) (oLen := oQLen) hP F X v6 R
      (by show slot (cwX s₀) 8 ≤ slot (cwX s₀) 8 + slot (cwP s₀) 24; omega_arith)
      (by have : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl; omega_arith) (oQa_al _) (by decide) X.x5 mQb
      mQ1 mQo hP.qk (by decide) (by decide) F.hDQ F.hQL) fun u ⟨R', h6, h11, h9, h10⟩ => ?_
    simp only [List.map_cons, List.map_nil, R'.a7, R'.ra, R'.s5, R'.t0, h6, h11, h9, h10]
  · obtain ⟨eS, ek, ep, eq, -, -, -, -, -, -, e4, -⟩ := data_vals h h'
    simp only [valsE, oQa, cwP, cwX, eS, ek, ep, eq, e4]

/-- The front and the powers, then `c`. -/
abbrev NM (c : Prog isa) : Prog isa := .seq (.block (Crt.save ++ Crt.args ++ setupX)) (mid1C c)

theorem nm_ok {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ : State} {c : Prog isa}
    {Q : State → Prop} (h : C0 d s₀) (hc : ∀ s t, PF s₀ → Front s₀ s → M1 s₀ s t → WP isa c t Q) :
    WP isa (NM c) s₀ Q :=
  WP.seq (WP.mono (front_ok s₀ h.1) fun s F => mid1_ok (pre_facts h.1) F fun t M => hc s t (pre_facts h.1) F M)

/-- `exportM2`'s first block. -/
abbrev EX1 : List Instr :=
  PublicChecked.base .t4 4 ++ [.load .d .t5 .s6 oQLen, .add .t4 .t4 .t5, .addi .t4 .t4 (-1)] ++ xb .t3 1

theorem pins248 : Pins (At C0 crtF 248) [.s6, .s11, .t3, .t4, .t5] := by
  refine pins_at_list (fun s₀ => [cS s₀, BitVec.ofNat 64 (8 * (cwX s₀ + 2)), Mont.off (cS s₀) (slot (cwX s₀) 1),
      Mont.off (Mont.off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 4 + (cqL s₀ - 1)), BitVec.ofNat 64 (cqL s₀)])
    (fun _ s₀ h => WP.of_flat (c := NM (.block EX1)) (by decide +kernel) (nm_ok h fun s t hP F M => ?_))
    fun _ _ _ h h' => ?_
  · have room := hP.room
    have hZ : 256 ≤ cZ s₀ := by unfold slot at room; omega_arith
    refine WP.mono (ex1_ok (L := cqL s₀) (F.scr.congr M.keep.2.2) M.a7 M.s5 M.s6 M.s11
      ((hdr_mid M.fr hZ (by unfold oQLen oMask; omega_arith)).trans F.hQL) hP.q1 (by omega_arith))
      fun u ⟨⟨a4, a5, a3⟩, k⟩ => ?_
    simp only [List.map_cons, List.map_nil, a3, a4, a5, k.gpr (r := .s6) (by decide), k.gpr (r := .s11) (by decide),
      M.s6, M.s11]
  · obtain ⟨eS, ek, ep, eq, -⟩ := data_vals h h'
    simp only [oQa, cwP, cwQ, cwX, eS, ek, ep, eq]

theorem pins250 : Pins (At C0 crtF 250) rsP := by
  refine pins_at_list (fun s₀ => valsP s₀ (oPa s₀) (cpL s₀))
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NM (.seq exportM2 (.seq (.block (setupP oBP oPLen)) (.block []))))
      (by decide +kernel) (nm_ok h fun s t hP F M => m2A_ok hP F M fun u Y h2 => wp_nil ?_)))
    fun _ _ _ h h' => ?_
  · simp only [List.map_cons, List.map_nil, Y.R.a7, Y.R.ra, Y.R.s5, Y.R.t0, h2, Y.s6, Y.s11]
  · obtain ⟨eS, ek, ep, -⟩ := data_vals h h'
    simp only [valsP, oPa, cwX, eS, ek, ep]

theorem pins251 : Pins (At C0 crtF 251) [.a7, .ra, .s5, .t0, .s6, .s11, .s10] := by
  refine pins_at_list (fun s₀ => [Mont.off (Mont.off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0),
      Mont.off (Mont.off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0), BitVec.ofNat 64 (8 * (cwP s₀ + 2)),
      BitVec.ofNat 64 (cwP s₀), cS s₀, BitVec.ofNat 64 (8 * (cwX s₀ + 2)), BitVec.ofNat 64 (cqL s₀)])
    (fun _ s₀ h => WP.of_flat (c := NM (.seq exportM2 (.seq (.block (setupP oBP oPLen))
      (.block [.load .d .s10 .s6 oQLen])))) (by decide +kernel) (nm_ok h fun s t hP F M => m2A_ok hP F M fun u Y _ => ?_))
    fun _ _ _ h h' => ?_
  · have room := hP.room
    have hZ : 256 ≤ cZ s₀ := by unfold slot at room; omega_arith
    have hs := F.scr.congr Y.wr
    have hL : u.mem.readW (cS s₀ + BitVec.ofNat 64 56) 64 = BitVec.ofNat 64 (cqL s₀) :=
      (hdr_mid (d := oQLen) Y.fr hZ (by unfold oQLen oMask; omega_arith)).trans F.hQL
    refine WP.mono (WP.keep [.s10] (Q := fun v => v.gpr .s10 = BitVec.ofNat 64 (cqL s₀)) ?_ (by rfl) (by rfl))
      fun v ⟨a10, k⟩ => ?_
    · brun [Y.s6, oQLen, hs.ld (show 56 + 8 ≤ cZ s₀ by omega_arith), hs.al8 (show 56 + 8 ≤ cZ s₀ by omega_arith) (by decide),
        hL]
    · simp only [List.map_cons, List.map_nil, a10, k.gpr (r := .a7) (by decide), k.gpr (r := .ra) (by decide),
        k.gpr (r := .s5) (by decide), k.gpr (r := .t0) (by decide), k.gpr (r := .s6) (by decide),
        k.gpr (r := .s11) (by decide), Y.R.a7, Y.R.ra, Y.R.s5, Y.R.t0, Y.s6, Y.s11]
  · obtain ⟨eS, ek, ep, eq, -⟩ := data_vals h h'
    simp only [oPa, cwP, cwX, eS, ek, ep, eq]

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

theorem valsW_eq {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ s₀' : State} (h : C0 d s₀)
    (h' : C0 d s₀') {o o' l l' : Nat} (xj : Nat) (ho : o = o') (hl : l = l') :
    valsW s₀ o l xj = valsW s₀' o' l' xj := by
  obtain ⟨eS, ek, -⟩ := data_vals h h'
  simp only [valsW, cwX, eS, ek, ho, hl]

theorem pins297 : Pins (At C0 crtF 297) rsW := by
  refine pins_at_list (fun s₀ => valsW s₀ (oPa s₀) (cpL s₀) 7)
    (fun _ s₀ h => WP.of_flat (c := NM (.seq exportM2 (.seq (.block (setupP oBP oPLen)) (.seq recombineP
      (.block (WD1 oBP oPLen 7)))))) (by decide +kernel)
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

theorem pins303 : Pins (At C0 crtF 303) rsW := by
  refine pins_at_list (fun s₀ => valsW s₀ (oQa s₀) (cqL s₀) 6)
    (fun _ s₀ h => WP.of_flat (c := NM (.seq exportM2 (.seq (.block (setupP oBP oPLen)) (.seq recombineP
      (.seq (widen oBP oPLen 7) (.block (WD1 oBQ oQLen 6))))))) (by decide +kernel)
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

theorem pins322 : Pins (At C0 crtF 322) [.a7, .s5, .s6, .s10, .s11] := by
  refine pins_at_list (fun s₀ => [Mont.off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (8 * (cwX s₀ + 2)), cS s₀,
      Mont.off (s₀.gpr .a0) 0, BitVec.ofNat 64 (ck s₀)])
    (fun _ s₀ h => WP.of_flat (c := NM (.seq exportM2 (.seq (.block (setupP oBP oPLen)) (.seq recombineP
      (.seq recombineX (.block finBlk)))))) (by decide +kernel)
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
