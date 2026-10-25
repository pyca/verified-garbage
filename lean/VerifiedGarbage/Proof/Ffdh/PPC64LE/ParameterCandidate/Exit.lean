module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.End
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubFn
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Entry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Range

/-!
# An FFDH parameter candidate on PPC64LE: the exit

`exit_ok`: the link register and the nonvolatile registers back from the
save area, memory unchanged.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search (ldh hWsLen)

theorem exitA_ok {p : PP} {t : State} (h : ESt p t) :
    WP isa (.block [ldh .r11 hWsLen, .lsl .r11 .r11 3, .add .r11 .r31 .r11, .subi .r11 .r11 saveBytes,
      .load .d .r0 .r11 144, .mtlr .r0]) t fun u =>
      u.gpr .r11 = off p.B (8 * p.n - 160) ∧ u.lr = p.sv 18 ∧ u.mem = t.mem ∧ u.rd = t.rd ∧ u.wr = t.wr ∧
        u.sp = t.sp ∧ ∀ r, r ≠ .r0 → r ≠ .r11 → u.gpr r = t.gpr r := by
  have hdn := h.dims.n
  have hb := h.dims.b1
  have hn' := h.dims.n'
  have hZe : p.Z = 8 * p.n := rfl
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have h8n : 160 ≤ 8 * p.n := by omega_arith
  have e1 : p.B + BitVec.ofNat 64 (8 * p.n) - BitVec.ofNat 64 160 = off p.B (8 * p.n - 160) :=
    VG.Offset.add_ofNat_sub p.B h8n
  have l0 : InRegions (t.rd ++ t.wr) (p.B + BitVec.ofNat 64 0) 8 := h.scr.ld (d := 0) (by omega_arith)
  have l144 : InRegions (t.rd ++ t.wr) (off p.B (8 * p.n - 160 + 144)) 8 := h.scr.ld (by omega_arith)
  have w0 : t.mem.readW (p.B + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 p.n := h.len
  have w144 : t.mem.readW (off p.B (8 * p.n - 160 + 144)) 64 = p.sv 18 := h.save 18 (by decide)
  simp only [ldh, hWsLen, saveBytes]
  prun [exec_mtlr, h.r31, l0, w0, Pub.ofNat_shl3, e1, l144, w144]
  intro r h0 h11
  simp only [h0, h11, ↓reduceIte]

local notation "sv" => Impl.Ffdh.PPC64LE.ParameterCandidate.saved

theorem sv_inj : ∀ i < 18, ∀ j < 18, sv i = sv j → i = j := by decide

theorem sv_ne11 : ∀ i < 18, sv i ≠ .r11 := by decide

/-- The first `k` registers restored to `v`, from the state `sB`. -/
structure XI (sB : State) (S : Addr) (v : Nat → BitVec 64) (k : Nat) (s : State) : Prop where
  r11 : s.gpr .r11 = S
  restored : ∀ i < k, s.gpr (sv i) = v i
  others : ∀ r, (∀ i < 18, r ≠ sv i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp
  lr : s.lr = sB.lr

theorem restore_step (sB : State) {S : Addr} {v : Nat → BitVec 64}
    (hin : ∀ i < 18, InRegions (sB.rd ++ sB.wr) (off S (8 * i)) 8)
    (hv : ∀ i < 18, sB.mem.readW (off S (8 * i)) 64 = v i)
    {k : Nat} (hk : k < 18) {s : State} (h : XI sB S v k s) :
    WP isa (.block [.load .d (sv k) .r11 (8 * k)]) s (XI sB S v (k + 1)) := by
  have hin' : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [h.rd, h.wr, h.r11]; exact hin k hk
  have hv' : s.mem.readW (S + BitVec.ofNat 64 (8 * k)) 64 = v k := by rw [h.mem]; exact hv k hk
  have hn11 := sv_ne11 k hk
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r11 ≠ .r0 by decide) (show 8 * k < 2 ^ 15 ∧ (8 * k) % 4 = 0 by omega_arith) hin',
    Option.some.injEq, exists_eq_left', h.r11, hv']
  refine ⟨?_, fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp, h.lr⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (Ne.symm hn11)]; exact h.r11
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : sv i ≠ sv k := fun e => absurd (sv_inj i (by omega_arith) k hk e) (by omega_arith)
      rw [ite_eq_right_iff.mpr fun e' => absurd e' e]; exact h.restored i hi
    · rw [ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (hr k hk)]
    exact h.others r hr

/-- The exit: the registers and the link register back from the save area. -/
theorem exit_ok {p : PP} {t : State} (h : ESt p t) :
    WP isa (.block exit) t fun u =>
      (∀ i < 18, u.gpr (sv i) = p.sv i) ∧ u.lr = p.sv 18 ∧ u.mem = t.mem ∧ u.sp = t.sp ∧
        ∀ r, r ≠ .r0 → r ≠ .r11 → (∀ i < 18, r ≠ sv i) → u.gpr r = t.gpr r := by
  have hdn := h.dims.n
  have hb := h.dims.b1
  have hn' := h.dims.n'
  have hZe : p.Z = 8 * p.n := rfl
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  unfold exit
  rw [map_flatMap, WP.block_append_iff]
  refine WP.mono (exitA_ok h) fun sB ⟨b11, blr, bm, brd, bwr, bsp, bo⟩ => ?_
  have hin : ∀ i < 18, InRegions (sB.rd ++ sB.wr) (off (off p.B (8 * p.n - 160)) (8 * i)) 8 := fun i hi => by
    rw [brd, bwr, show off (off p.B (8 * p.n - 160)) (8 * i) = off p.B (8 * p.n - 160 + 8 * i) by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
    exact h.scr.ld (by omega_arith)
  have hv : ∀ i < 18, sB.mem.readW (off (off p.B (8 * p.n - 160)) (8 * i)) 64 = p.sv i := fun i hi => by
    rw [bm, show off (off p.B (8 * p.n - 160)) (8 * i) = off p.B (8 * p.n - 160 + 8 * i) by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
    exact h.save i (by omega_arith)
  refine WP.mono (wp_range_flatMap (M := isa) (XI sB (off p.B (8 * p.n - 160)) p.sv)
    (fun k s hk hs => restore_step sB hin hv hk hs) 18 (Nat.le_refl _) sB
    ⟨b11, fun _ h => absurd h (by omega_arith), fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩) fun u hu => ?_
  exact ⟨hu.restored, by rw [hu.lr, blr], by rw [hu.mem, bm], by rw [hu.sp, bsp],
    fun r h0 h11 hs => by rw [hu.others r hs, bo r h0 h11]⟩

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
