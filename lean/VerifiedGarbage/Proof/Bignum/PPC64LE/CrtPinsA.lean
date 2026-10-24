module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCTBase
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Reach
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPre
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtLoadX
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# The RSA private-key operation on PPC64LE: the registers at the cuts of `loadX`

The code's list of programs (`crtF`) is cut after each block that loads a
buffer's address and length from the header, and after `n`'s first byte
(`check1`): the registers there, from the initial state (`pins*`). In
`loadX`, `XI` is what a buffer's load needs: the registers of `X` and the
header as the front left it.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE (Pins At pins_at_list)

/-- The code's list of programs. -/
abbrev crtF : List (Prog isa) := Code.flat crt

/-- In `loadX`, after the front left `s`. -/
structure XI (s₀ s t : State) : Prop where
  scr : Scr t (cS s₀) (cZ s₀)
  r23 : t.gpr .r23 = cS s₀
  r10 : t.gpr .r10 = off (cS s₀) (slot (cwX s₀) 0)
  r21 : t.gpr .r21 = off (cS s₀) (slot (cwX s₀) 0)
  r29 : t.gpr .r29 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  r11 : t.gpr .r11 = BitVec.ofNat 64 (2 * cwX s₀)
  r27 : t.gpr .r27 = off (cS s₀) (slot (cwX s₀) 0)
  r28 : t.gpr .r28 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  out : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem
  rd : t.rd ++ t.wr = s₀.rd ++ s₀.wr

theorem xi_front {s₀ s : State} (F : Front s₀ s) : XI s₀ s s :=
  ⟨F.scr, F.r23, F.r10, F.r21, F.r29, F.r11, F.r27, F.r28, Outside.refl _ _ _ _, by rw [F.keep.rd, F.keep.wr]⟩

theorem XI.hdr {s₀ s t : State} (hP : PF s₀) (X : XI s₀ s t) {d : Nat} (hd : d + 8 ≤ 256) :
    word t.mem (cS s₀) d = word s.mem (cS s₀) d := by
  have hn := hP.nw; have room := hP.room
  have : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
  exact X.out.word (Or.inl hd) (by omega)

/-- `XI` through code that keeps the registers and changes only the arrays. -/
theorem XI.step {s₀ s t u : State} (hP : PF s₀) (X : XI s₀ s t) {rs : List Reg} (k : Keep rs t u)
    (h : ∀ r ∈ [Reg.r23, .r21, .r29, .r11, .r27, .r28], r ∉ rs)
    (h10 : u.gpr .r10 = off (cS s₀) (slot (cwX s₀) 0))
    (o : Outside (cS s₀) 256 (slot (cwX s₀) 8 - 256) t.mem u.mem) : XI s₀ s u := by
  have room := hP.room
  have : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  exact ⟨X.scr.congr k.wr, (k.gpr _ h.1).trans X.r23, h10, (k.gpr _ h.2.1).trans X.r21,
    (k.gpr _ h.2.2.1).trans X.r29, (k.gpr _ h.2.2.2.1).trans X.r11, (k.gpr _ h.2.2.2.2.1).trans X.r27,
    (k.gpr _ h.2.2.2.2.2).trans X.r28, X.out.trans (o.mono (Nat.le_refl _) (by omega)),
    by rw [k.rd, k.wr]; exact X.rd⟩

/-- `r14 := r10`, then `X`'s array 0 := all ones. -/
theorem xi_ones {s₀ s t : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (X : XI s₀ s t)
    (hc : ∀ u, XI s₀ s u → WP isa c u Q) :
    WP isa (.seq (.block [.addi .r14 .r10 0]) (.seq onesWords c)) t Q := by
  have room := hP.room; have k64 := hP.k64; have k1024 := hP.k1024
  have e0 : slot (cwX s₀) 0 = 256 + 0 * (8 * (cwX s₀ + 2)) := rfl
  have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  refine WP.seq (WP.mono (WP.keep [.r14] (Q := fun u => u.gpr .r14 = off (cS s₀) (slot (cwX s₀) 0) ∧
    u.mem = t.mem) (by prun [X.r10, BitVec.add_zero]) (by decide)) fun t₁ ⟨⟨a14, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (onesWords_ok (X.scr.congr k1.wr) a14 ((k1.gpr _ (by decide)).trans X.r11) (by omega)
    (by omega) (by omega)) fun t₂ ⟨⟨_, o2⟩, k2⟩ => hc t₂ ?_)
  rw [m1] at o2
  exact XI.step hP X (k1.trans k2) (by decide) (((k1.trans k2).gpr _ (by decide)).trans X.r10)
    (o2.mono (by omega) (by omega))

/-- A buffer's address and length from the header's words `oA`, `oL`. -/
theorem ld2_ok {s₀ s t : State} {oA oL : Nat} {A : Addr} {L : Nat} (hP : PF s₀) (X : XI s₀ s t)
    (hoA : oA + 8 ≤ 256 ∧ oA % 8 = 0) (hoL : oL + 8 ≤ 256 ∧ oL % 8 = 0)
    (hA : word s.mem (cS s₀) oA = off A 0) (hLw : word s.mem (cS s₀) oL = BitVec.ofNat 64 L) :
    WP isa (.block [.load .d .r12 .r23 oA, .load .d .r6 .r23 oL]) t fun u =>
      (u.gpr .r12 = off A 0 ∧ u.gpr .r6 = BitVec.ofNat 64 L ∧ u.mem = t.mem) ∧ Keep [.r12, .r6] t u := by
  have room := hP.room
  have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
  have hA' : t.mem.readW (off (cS s₀) oA) 64 = off A 0 := by rw [← hA]; exact X.hdr hP hoA.1
  have hL' : t.mem.readW (off (cS s₀) oL) 64 = BitVec.ofNat 64 L := by rw [← hLw]; exact X.hdr hP hoL.1
  refine WP.keep _ ?_ rfl
  prun [X.r23, exec_load_d (show Reg.r23 ≠ .r0 by decide) ⟨show oA < 2 ^ 15 by omega, show oA % 4 = 0 by omega⟩,
    exec_load_d (show Reg.r23 ≠ .r0 by decide) ⟨show oL < 2 ^ 15 by omega, show oL % 4 = 0 by omega⟩,
    X.scr.ld (show oA + 8 ≤ cZ s₀ by omega), X.scr.ld (show oL + 8 ≤ cZ s₀ by omega), hA', hL']

/-- A buffer into `X`'s array `j`. -/
theorem xi_load {s₀ s t : State} {c : Prog isa} {Q : State → Prop} {j oA oL : Nat} {A : Addr} {L : Nat}
    (hP : PF s₀) (X : XI s₀ s t) (hj : j < 8)
    (hoA : oA + 8 ≤ 256 ∧ oA % 8 = 0) (hoL : oL + 8 ≤ 256 ∧ oL % 8 = 0)
    (hA : word s.mem (cS s₀) oA = off A 0) (hLw : word s.mem (cS s₀) oL = BitVec.ofNat 64 L) (hL : 1 ≤ L)
    (hLk : L ≤ ck s₀) (hrd : ∀ i < L, InRegions (s₀.rd ++ s₀.wr) (off A i) 1)
    (hsep : ∀ i < L, ∀ x, ofs (cS s₀) x < cZ s₀ → off A i ≠ x)
    (hc : ∀ u, XI s₀ s u → WP isa c u Q) :
    WP isa (.seq (.seq (.block [.load .d .r12 .r23 oA, .load .d .r6 .r23 oL]) (loadArr j)) c) t Q := by
  have room := hP.room; have k64 := hP.k64; have k1024 := hP.k1024
  have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  refine WP.seq (WP.mono (loadOne_ok X.scr (by omega) hj (by omega) X.r23 X.r10 X.r21 X.r29 X.r11 hoA hoL
    (by rw [X.hdr hP hoA.1]; exact hA) (by rw [X.hdr hP hoL.1]; exact hLw) hL (by omega)
    (by rw [X.rd]; exact hrd) hsep) fun u ⟨⟨_, _, o, u10⟩, k⟩ => hc u ?_)
  have := slot_le (w := cwX s₀) hj
  have h256 : 256 ≤ slot (cwX s₀) j := Nat.le_add_right _ _
  exact XI.step hP X k (by decide) u10 (o.mono (by omega) (by omega))

/-- The registers after a buffer's address and length. -/
theorem xi_ld {s₀ s t : State} {oA oL : Nat} {A : Addr} {L : Nat} (hP : PF s₀) (X : XI s₀ s t)
    (hoA : oA + 8 ≤ 256 ∧ oA % 8 = 0) (hoL : oL + 8 ≤ 256 ∧ oL % 8 = 0)
    (hA : word s.mem (cS s₀) oA = off A 0) (hLw : word s.mem (cS s₀) oL = BitVec.ofNat 64 L) :
    WP isa (.block [.load .d .r12 .r23 oA, .load .d .r6 .r23 oL]) t fun u =>
      [Reg.r6, .r10, .r11, .r12, .r21, .r23, .r29].map u.gpr =
        [BitVec.ofNat 64 L, off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (2 * cwX s₀), off A 0,
          off (cS s₀) (slot (cwX s₀) 0), cS s₀, BitVec.ofNat 64 (8 * (cwX s₀ + 2))] :=
  WP.mono (ld2_ok hP X hoA hoL hA hLw) fun u ⟨⟨a12, a6, _⟩, k⟩ => by
    simp only [List.map_cons, List.map_nil, a12, a6, k.gpr .r10 (by decide), k.gpr .r11 (by decide),
      k.gpr .r21 (by decide), k.gpr .r23 (by decide), k.gpr .r29 (by decide), X.r10, X.r11, X.r21, X.r23, X.r29]

/-- What two initial states with the same public data share. -/
theorem data_vals {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ s₀' : State} (h : C0 d s₀)
    (h' : C0 d s₀') :
    cS s₀ = cS s₀' ∧ ck s₀ = ck s₀' ∧ cpL s₀ = cpL s₀' ∧ cqL s₀ = cqL s₀' ∧ s₀.gpr .r3 = s₀'.gpr .r3 ∧
      s₀.gpr .r5 = s₀'.gpr .r5 ∧ s₀.gpr .r7 = s₀'.gpr .r7 ∧ s₀.gpr .r9 = s₀'.gpr .r9 ∧
      stackArg s₀ 0 = stackArg s₀' 0 ∧ stackArg s₀ 2 = stackArg s₀' 2 ∧ stackArg s₀ 4 = stackArg s₀' 4 ∧
      stackArg s₀ 6 = stackArg s₀' 6 ∧
      Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r5) (ck s₀) = Spec.Rsa.bytesAt s₀'.mem (s₀'.gpr .r5) (ck s₀') := by
  have E := two_data h h'
  exact ⟨E.sa 8 (by decide), by simp only [ck, E.r6], by simp only [cpL, E.r10], by show (stackArg s₀ 1).toNat = (stackArg s₀' 1).toNat; rw [E.sa 1 (by decide)],
    E.r3, E.r5, E.r7, E.r9, E.sa 0 (by decide), E.sa 2 (by decide), E.sa 4 (by decide), E.sa 6 (by decide), E.nb⟩

/-- The registers at the cut after a buffer's address and length. -/
abbrev ldVals (s₀ : State) (A : Addr) (L : Nat) : List (BitVec 64) :=
  [BitVec.ofNat 64 L, off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (2 * cwX s₀), off A 0,
    off (cS s₀) (slot (cwX s₀) 0), cS s₀, BitVec.ofNat 64 (8 * (cwX s₀ + 2))]

theorem pins1 : Pins (At C0 crtF 1) [.r10, .r11, .r23] := by
  refine pins_at_list (fun s₀ => [off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (2 * cwX s₀), cS s₀])
    (fun _ s₀ h => WP.of_flat (c := .block (Crt.save ++ Crt.args ++ setupX)) rfl
      (WP.mono (front_ok s₀ h.1) fun s F => by simp only [List.map_cons, List.map_nil, F.r10, F.r11, F.r23]))
    fun _ s₀ s₀' h h' => ?_
  obtain ⟨eS, ek, -⟩ := data_vals h h'
  simp only [cwX, eS, ek]

/-- A buffer's address and length, as a block. -/
abbrev LD (oA oL : Nat) : Prog isa := .block [.load .d .r12 .r23 oA, .load .d .r6 .r23 oL]

/-- The front, then `X`'s array 0 := all ones, then `c`. -/
abbrev N0 (c : Prog isa) : Prog isa :=
  .seq (.block (Crt.save ++ Crt.args ++ setupX)) (.seq (.block [.addi .r14 .r10 0]) (.seq onesWords c))

/-- A buffer into array `j`, then `c`. -/
abbrev LJ (j oA oL : Nat) (c : Prog isa) : Prog isa := .seq (.seq (LD oA oL) (loadArr j)) c

theorem xi_start {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ : State} {c : Prog isa}
    {Q : State → Prop} (h : C0 d s₀) (hc : ∀ s t, PF s₀ → Front s₀ s → XI s₀ s t → WP isa c t Q) :
    WP isa (N0 c) s₀ Q :=
  WP.seq (WP.mono (front_ok s₀ h.1) fun s F => xi_ones (pre_facts h.1) (xi_front F) fun t X =>
    hc s t (pre_facts h.1) F X)

theorem ldVals_eq {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ s₀' : State} (h : C0 d s₀)
    (h' : C0 d s₀') {A A' : Addr} {L L' : Nat} (hA : A = A') (hL : L = L') :
    ldVals s₀ A L = ldVals s₀' A' L' := by
  obtain ⟨eS, ek, -⟩ := data_vals h h'
  simp only [ldVals, cwX, eS, ek, hA, hL]

theorem pins5 : Pins (At C0 crtF 5) [.r6, .r10, .r11, .r12, .r21, .r23, .r29] :=
  pins_at_list (fun s₀ => ldVals s₀ (s₀.gpr .r5) (ck s₀))
    (fun _ s₀ h => WP.of_flat (c := N0 (LD oN oNLen)) rfl (xi_start h fun _ _ hP F X =>
      xi_ld hP X (by decide) (by decide) F.hN F.hNL))
    fun _ _ _ h h' => let E := data_vals h h'; ldVals_eq h h' E.2.2.2.2.2.1 E.2.1

theorem pins13 : Pins (At C0 crtF 13) [.r6, .r10, .r11, .r12, .r21, .r23, .r29] :=
  pins_at_list (fun s₀ => ldVals s₀ (s₀.gpr .r9) (cpL s₀))
    (fun _ s₀ h => WP.of_flat (c := N0 (LJ 1 oN oNLen (LD oP oPLen))) rfl (xi_start h fun _ _ hP F X =>
      xi_load (j := 1) hP X (by decide) (by decide) (by decide) F.hN F.hNL (by have := hP.k64; omega)
        (Nat.le_refl _) hP.rN hP.sN fun _ X =>
      xi_ld hP X (by decide) (by decide) F.hP F.hPL))
    fun _ _ _ h h' => let E := data_vals h h'; ldVals_eq h h' E.2.2.2.2.2.2.2.1 E.2.2.1

theorem pins21 : Pins (At C0 crtF 21) [.r6, .r10, .r11, .r12, .r21, .r23, .r29] :=
  pins_at_list (fun s₀ => ldVals s₀ (stackArg s₀ 0) (cqL s₀))
    (fun _ s₀ h => WP.of_flat (c := N0 (LJ 1 oN oNLen (LJ 4 oP oPLen (LD oQ oQLen)))) rfl
      (xi_start h fun _ _ hP F X =>
      xi_load (j := 1) hP X (by decide) (by decide) (by decide) F.hN F.hNL (by have := hP.k64; omega)
        (Nat.le_refl _) hP.rN hP.sN fun _ X =>
      xi_load (j := 4) hP X (by decide) (by decide) (by decide) F.hP F.hPL hP.p1 (Nat.le_of_lt hP.pk)
        hP.rP hP.sP fun _ X =>
      xi_ld hP X (by decide) (by decide) F.hQ F.hQL))
    fun _ _ _ h h' => let E := data_vals h h'; ldVals_eq h h' E.2.2.2.2.2.2.2.2.1 E.2.2.2.1

theorem pins29 : Pins (At C0 crtF 29) [.r6, .r10, .r11, .r12, .r21, .r23, .r29] :=
  pins_at_list (fun s₀ => ldVals s₀ (s₀.gpr .r7) (ck s₀))
    (fun _ s₀ h => WP.of_flat (c := N0 (LJ 1 oN oNLen (LJ 4 oP oPLen (LJ 5 oQ oQLen (LD oIn oNLen))))) rfl
      (xi_start h fun _ _ hP F X =>
      xi_load (j := 1) hP X (by decide) (by decide) (by decide) F.hN F.hNL (by have := hP.k64; omega)
        (Nat.le_refl _) hP.rN hP.sN fun _ X =>
      xi_load (j := 4) hP X (by decide) (by decide) (by decide) F.hP F.hPL hP.p1 (Nat.le_of_lt hP.pk)
        hP.rP hP.sP fun _ X =>
      xi_load (j := 5) hP X (by decide) (by decide) (by decide) F.hQ F.hQL hP.q1 (Nat.le_of_lt hP.qk)
        hP.rQ hP.sQ fun _ X =>
      xi_ld hP X (by decide) (by decide) F.hIn F.hNL))
    fun _ _ _ h h' => let E := data_vals h h'; ldVals_eq h h' E.2.2.2.2.2.2.1 E.2.1

theorem pins37 : Pins (At C0 crtF 37) [.r6, .r10, .r11, .r12, .r21, .r23, .r29] :=
  pins_at_list (fun s₀ => ldVals s₀ (stackArg s₀ 6) (cpL s₀))
    (fun _ s₀ h => WP.of_flat
      (c := N0 (LJ 1 oN oNLen (LJ 4 oP oPLen (LJ 5 oQ oQLen (LJ 6 oIn oNLen (LD oQInv oPLen)))))) rfl
      (xi_start h fun _ _ hP F X =>
      xi_load (j := 1) hP X (by decide) (by decide) (by decide) F.hN F.hNL (by have := hP.k64; omega)
        (Nat.le_refl _) hP.rN hP.sN fun _ X =>
      xi_load (j := 4) hP X (by decide) (by decide) (by decide) F.hP F.hPL hP.p1 (Nat.le_of_lt hP.pk)
        hP.rP hP.sP fun _ X =>
      xi_load (j := 5) hP X (by decide) (by decide) (by decide) F.hQ F.hQL hP.q1 (Nat.le_of_lt hP.qk)
        hP.rQ hP.sQ fun _ X =>
      xi_load (j := 6) hP X (by decide) (by decide) (by decide) F.hIn F.hNL (by have := hP.k64; omega)
        (Nat.le_refl _) hP.rI hP.sI fun _ X =>
      xi_ld hP X (by decide) (by decide) F.hQI F.hPL))
    fun _ _ _ h h' => let E := data_vals h h'; ldVals_eq h h' E.2.2.2.2.2.2.2.2.2.2.2.1 E.2.2.1

/-- `loadX`, from the front, then `c`. -/
abbrev NX (c : Prog isa) : Prog isa :=
  N0 (LJ 1 oN oNLen (LJ 4 oP oPLen (LJ 5 oQ oQLen (LJ 6 oIn oNLen (LJ 7 oQInv oPLen c)))))

theorem xi_loadX {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ : State} {c : Prog isa}
    {Q : State → Prop} (h : C0 d s₀) (hc : ∀ s t, PF s₀ → Front s₀ s → XI s₀ s t → WP isa c t Q) :
    WP isa (NX c) s₀ Q :=
  xi_start h fun s _ hP F X =>
    xi_load (j := 1) hP X (by decide) (by decide) (by decide) F.hN F.hNL (by have := hP.k64; omega)
      (Nat.le_refl _) hP.rN hP.sN fun _ X =>
    xi_load (j := 4) hP X (by decide) (by decide) (by decide) F.hP F.hPL hP.p1 (Nat.le_of_lt hP.pk)
      hP.rP hP.sP fun _ X =>
    xi_load (j := 5) hP X (by decide) (by decide) (by decide) F.hQ F.hQL hP.q1 (Nat.le_of_lt hP.qk)
      hP.rQ hP.sQ fun _ X =>
    xi_load (j := 6) hP X (by decide) (by decide) (by decide) F.hIn F.hNL (by have := hP.k64; omega)
      (Nat.le_refl _) hP.rI hP.sI fun _ X =>
    xi_load (j := 7) hP X (by decide) (by decide) (by decide) F.hQI F.hPL hP.p1 (Nat.le_of_lt hP.pk)
      hP.rQI hP.sQI fun t X => hc s t hP F X

theorem pins45 : Pins (At C0 crtF 45) [.r6, .r12] :=
  pins_at_list (fun s₀ => [BitVec.ofNat 64 (ck s₀), off (s₀.gpr .r5) 0])
    (fun _ s₀ h => WP.of_flat (c := NX (LD oN oNLen)) rfl (xi_loadX h fun _ _ hP F X =>
      WP.mono (ld2_ok hP X (by decide) (by decide) F.hN F.hNL) fun u ⟨⟨a12, a6, _⟩, _⟩ => by
        simp only [List.map_cons, List.map_nil, a12, a6]))
    fun _ _ _ h h' => by
      obtain ⟨-, ek, -, -, -, e5, -⟩ := data_vals h h'
      rw [ek, e5]

/-- `n`'s first byte. -/
abbrev nb0 (s₀ : State) : BitVec 64 :=
  BitVec.ofNat 64 ((Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r5) (ck s₀)).getD 0 0).toNat

theorem pins46 : Pins (At C0 crtF 46) [.r6, .r10, .r11, .r15, .r21, .r23, .r27, .r28, .r29] := by
  refine pins_at_list (fun s₀ => [BitVec.ofNat 64 (ck s₀), off (cS s₀) (slot (cwX s₀) 0),
      BitVec.ofNat 64 (2 * cwX s₀), nb0 s₀, off (cS s₀) (slot (cwX s₀) 0), cS s₀,
      off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (8 * (cwX s₀ + 2)), BitVec.ofNat 64 (8 * (cwX s₀ + 2))])
    (fun _ s₀ h => WP.of_flat (c := NX (.seq (LD oN oNLen) (.block Precompute.check1))) rfl (xi_loadX h fun s t hP F X => ?_))
    fun _ _ _ h h' => ?_
  · have hn := hP.nw; have room := hP.room; have k64 := hP.k64
    have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
    refine WP.seq (WP.mono (ld2_ok hP X (by decide) (by decide) F.hN F.hNL) fun u ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
    refine WP.mono (VG.Proof.Bignum.PPC64LE.check1_ok (nb := Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r5) (ck s₀)) a12 a6 k64
      (VG.Proof.Bignum.bytesAt_length _ _ _) (by rw [k1.rd, k1.wr, X.rd]; exact hP.rN) fun i hi => ?_)
      fun v ⟨⟨_, v15, _, _⟩, k2⟩ => ?_
    · have hs := hP.sN i hi
      have hx : ¬ ofs (cS s₀) (Mont.off (s₀.gpr .r5) i) < cZ s₀ := fun hc => hs _ hc rfl
      rw [m1, X.out _ (Or.inr (by omega)), F.mem _ (Or.inr (by omega))]
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    · have k12 := k1.trans k2
      simp only [List.map_cons, List.map_nil, v15, k2.gpr .r6 (by decide), a6, k12.gpr .r10 (by decide),
        k12.gpr .r11 (by decide), k12.gpr .r21 (by decide), k12.gpr .r23 (by decide), k12.gpr .r27 (by decide),
        k12.gpr .r28 (by decide), k12.gpr .r29 (by decide), X.r10, X.r11, X.r21, X.r23, X.r27, X.r28, X.r29,
        nb0, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 0 < (Spec.Rsa.bytesAt s₀.mem
          (s₀.gpr .r5) (ck s₀)).length by rw [VG.Proof.Bignum.bytesAt_length]; omega), Option.getD_some]
  · obtain ⟨eS, ek, -, -, -, -, -, -, -, -, -, -, en⟩ := data_vals h h'
    simp only [nb0, cwX]; rw [en, eS, ek]

end VG.Proof.Bignum.PPC64LE.Crt
