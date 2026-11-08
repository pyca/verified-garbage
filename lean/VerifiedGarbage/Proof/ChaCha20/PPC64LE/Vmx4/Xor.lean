module

public import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Vmx4.Chunk
public import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Xor
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Vmx4.Chunk
meta import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Xor
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Call
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public meta import VerifiedGarbage.Impl.ChaCha20.PPC64LE.Vmx4

/-! # The four-block ChaCha20 keystream XOR on PPC64LE

The chunks (`bulk_ok`), then `Xor.xor` on the rest, proven against the
contract on its own entry (`rest_ok`): `xor_correct`. -/

@[expose] public section

namespace VG.Proof.ChaCha20.PPC64LE.Vmx4

open VG VG.PPC64LE VG.Impl.ChaCha20.PPC64LE.Vmx4
open VG.Proof.ChaCha20 (ctr length_keystream keystream_getD bytesAt_xor_to xorPPC64LE)
open VG.Proof.ChaCha20.PPC64LE.Xor (XPre st srp L bp dp stR srR dR bR S0 X0 D0 KS Dst Src L_lt)
open VG.Spec.ChaCha20 (stateAt keystream serialize block bytesAt)

/-! ## The rest of the data

After the chunks, `Xor.xor` runs on the rest of the source and of the
destination, proven against the contract on its own entry. -/

/-- The source and the destination after their first `n` bytes. -/
abbrev srcRest (s₀ : State) (n : Nat) : Region := ⟨srp s₀ + BitVec.ofNat 64 n, L s₀ - n⟩
abbrev dstRest (s₀ : State) (n : Nat) : Region := ⟨dp s₀ + BitVec.ofNat 64 n, L s₀ - n⟩

theorem ctr_ctr (S : CState) (a b : Nat) : ctr (ctr S a) b = ctr S (a + b) := by
  simp only [ctr, Vector.getElem_set_self, Vector.set_set, BitVec.ofNat_add, BitVec.add_assoc]

/-- A byte of the destination, from the source XORed with a keystream. -/
theorem bytes_of_to {m m' : Mem} {p q : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : Spec.ChaCha20.bytesAt m' q n = List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt m p n) ks)
    {k : Nat} (hk : k < n) :
    m' (q + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) ^^^ ks.getD k 0 := by
  have e := congrArg (fun l => l[k]?) h
  simp only [Spec.ChaCha20.bytesAt, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    List.getElem?_zipWith, List.getElem?_eq_getElem (show k < ks.length by omega)] at e
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < ks.length by omega),
    Option.getD_some]
  simpa using e

theorem not_rest {s₀ : State} {n k : Nat} (hk : k < n) (hn : n ≤ L s₀) :
    ¬ (dstRest s₀ n).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL := L_lt s₀
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega) (by omega)]
  split <;> omega

theorem lr_withRegions (s : State) (rd wr : List Region) : (s.withRegions rd wr).lr = s.lr := rfl

/-- `Xor.xor` on the rest after the first `n` bytes (a multiple of 64), from
a state with the source and the destination done up to there: the
contract's postcondition for the whole. -/
theorem rest_ok {s₀ s : State} {n : Nat} (hp : XPre s₀) (hn : n ≤ L s₀) (h64 : n % 64 = 0)
    (h3 : s.gpr .r3 = st s₀) (h4 : s.gpr .r4 = srp s₀ + BitVec.ofNat 64 n)
    (h5 : s.gpr .r5 = BitVec.ofNat 64 (L s₀ - n)) (h6 : s.gpr .r6 = bp s₀)
    (h7 : s.gpr .r7 = dp s₀ + BitVec.ofNat 64 n) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hcnt : stateAt s.mem (st s₀) = ctr (S0 s₀) (n / 64))
    (hd : Dst s₀ n s.mem) (hs : Src s₀ n s.mem) :
    WP isa VG.Impl.ChaCha20.PPC64LE.Xor.xor s fun u => abiPreserved s u ∧ xorPPC64LE.post s₀ u := by
  have hL := L_lt s₀
  have hN : (BitVec.ofNat 64 (L s₀ - n)).toNat = L s₀ - n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have ts : Region.Sub (srcRest s₀ n) (srR s₀) := Offset.sub_base _ (by omega)
  have tt : Region.Sub (dstRest s₀ n) (dR s₀) := Offset.sub_base _ (by omega)
  have hpre : xorPPC64LE.pre (s.withRegions [srcRest s₀ n] [stR s₀, dstRest s₀ n, bR s₀]) := by
    simp only [xorPPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, h3, h4, h5, h6, h7, hN]
    refine ⟨trivial, trivial, hp.st_s.sub_right ts, hp.st_d.sub_right tt, hp.st_b, hp.s_b.sub_left ts,
      hp.d_b.sub_left tt, ?_, ?_, ?_⟩
    · rcases hp.alias with he | hdis
      · exact .inl (by rw [he])
      · exact .inr ((hdis.sub_left ts).sub_right tt)
    · have := hp.snowrap; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · have := hp.nowrap; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hcw : Covers [stR s₀, dstRest s₀ n, bR s₀] s.wr := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dR s₀, by simp, n, rfl, by dsimp; omega⟩
    · exact ⟨bR s₀, by simp, 0, by simp, by simp⟩
  have hcr : Covers [srcRest s₀ n] s.rd := by
    rw [hrd, hp.rd]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨srR s₀, by simp, n, rfl, by dsimp; omega⟩
  refine WP.narrow (VG.Proof.ChaCha20.PPC64LE.Xor.xor_correct _ hpre)
    (Covers.append hcr hcw) hcw ?_ VG.Proof.ChaCha20.PPC64LE.Xor.xor_noFrames
  intro u _ _ _ hf ⟨ha, hpost⟩
  simp only [abiPreserved, State.withRegions_gpr, State.withRegions_sp, lr_withRegions] at ha
  simp only [xorPPC64LE, State.withRegions_gpr, State.withRegions_mem,
    h3, h4, h5, h7, hN, hcnt] at hpost
  refine ⟨ha, ?_⟩
  refine bytesAt_xor_to (length_keystream _ _) fun k hk => ?_
  have hk' : k < L s₀ := hk
  by_cases hkn : k < n
  · have ct : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
      Offset.contains_base _ (by omega) (by omega)
    rw [hf _ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact fun h => hp.st_d _ h ct
      · exact not_rest hkn hn
      · exact fun h => hp.d_b _ ct h), hd k hk', ite_eq_left hkn]
  · have x := bytes_of_to (length_keystream _ _) hpost (k := k - n)
      (show k - n < L s₀ - n by omega)
    rw [Offset.add_add, Offset.add_add, show n + (k - n) = k by omega, hs k hk' (by omega),
      keystream_getD _ (by omega), ctr_ctr,
      show n / 64 + (k - n) / 64 = k / 64 by omega, show (k - n) % 64 = k % 64 by omega] at x
    rw [x, keystream_getD _ hk']

/-! ## The chunks -/

/-- Before chunk `t`: the pointers and the length advanced, the destination
done up to there and the source after it intact, the counter advanced by
`4 t`. -/
structure LInv (s₀ : State) (t : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = st s₀
  r4 : s.gpr .r4 = srp s₀ + BitVec.ofNat 64 (256 * t)
  r5 : s.gpr .r5 = BitVec.ofNat 64 (L s₀ - 256 * t)
  r6 : s.gpr .r6 = bp s₀
  r7 : s.gpr .r7 = dp s₀ + BitVec.ofNat 64 (256 * t)
  r10 : s.gpr .r10 = s.syms tblName
  r11 : s.gpr .r11 = s₀.lr
  le : 256 * t ≤ L s₀
  keep : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) (4 * t)
  data : Dst s₀ (256 * t) s.mem
  src : Src s₀ (256 * t) s.mem

theorem preserved_ne : ∀ r ∈ preserved, r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r7 ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧
    r ≠ .r11 ∧ r ≠ .r12 := by decide

theorem shr8 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> 8 = BitVec.ofNat 64 (n / 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem ks_shift (S : CState) {len t k : Nat} (hk : k < len) (ht : 256 * t ≤ k) :
    (keystream S len).getD k 0 =
      (serialize (block (ctr (ctr S (4 * t)) ((k - 256 * t) / 64)))).getD
        ((k - 256 * t) % 64) 0 := by
  rw [keystream_getD _ hk, ctr_ctr, show 4 * t + (k - 256 * t) / 64 = k / 64 by omega,
    show (k - 256 * t) % 64 = k % 64 by omega]

/-- Advance the counter by four, the pointers by 256 bytes and the length by
256. -/
theorem next_ok {s₀ : State} (hp : XPre s₀) {s : State} (h3 : s.gpr .r3 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block next) s fun s' =>
      s'.gpr .r4 = s.gpr .r4 + BitVec.ofNat 64 256 ∧ s'.gpr .r7 = s.gpr .r7 + BitVec.ofNat 64 256 ∧
      s'.gpr .r5 = s.gpr .r5 - BitVec.ofNat 64 256 ∧
      s'.gpr .r9 = (s.gpr .r5 - BitVec.ofNat 64 256) >>> 8 ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r7 → r ≠ .r8 → r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      stateAt s'.mem (st s₀) = ctr (stateAt s.mem (st s₀)) 4 ∧
      Frame [stR s₀] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧
      s'.syms = s.syms := by
  have c₁ : (stR s₀).Contains (st s₀ + BitVec.ofNat 64 48) 4 :=
    Offset.contains_base _ (by decide) (by decide)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 48) 4 :=
    ⟨stR s₀, by simp [hrd, hwr, hp.rd, hp.wr], by rw [h3]; exact c₁⟩
  let s₁ := s.write .r8 ((s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 48) 32).setWidth 64)
  let s₂ := s₁.write .r8 (s₁.gpr .r8 + BitVec.ofNat 64 4)
  have hout : InRegions s₂.wr (s₂.gpr .r3 + BitVec.ofNat 64 48) 4 :=
    ⟨stR s₀, by simp [s₂, s₁, RegUpd.wr_write, hwr, hp.wr], by
      simp only [s₂, s₁, RegUpd.gpr_write_of_ne _ _ (show Reg.r3 ≠ .r8 by decide), h3]; exact c₁⟩
  apply WP.of_runBlock
  simp only [next, runBlock_cons, exec_load_w (show Reg.r3 ≠ .r0 by decide) (by decide) hin,
    runStep_some, exec_addi (show Reg.r8 ≠ .r0 by decide) (show 4 < 2 ^ 15 by decide)]
  rw [exec_store_w (show Reg.r3 ≠ .r0 by decide) (by decide) hout]
  simp only [runStep_some, runBlock_cons, runBlock_nil,
    exec_addi (show Reg.r4 ≠ .r0 by decide) (show 256 < 2 ^ 15 by decide),
    exec_addi (show Reg.r7 ≠ .r0 by decide) (show 256 < 2 ^ 15 by decide),
    exec_subi (show Reg.r5 ≠ .r0 by decide) (show 256 ≤ 2 ^ 15 by decide),
    exec_lsr_d (show 8 < 64 by decide), Option.some.injEq, exists_eq_left']
  have hv : s.mem.readW (st s₀ + BitVec.ofNat 64 48) 32 = (stateAt s.mem (st s₀))[12] := by
    simp [stateAt]
  refine ⟨?_, ?_, ?_, ?_, fun r h4 h5 h7 h8 h9 => ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  all_goals simp only [s₂, s₁, RegUpd.gpr_write, RegUpd.mem_write, reduceCtorEq, ite_true, ite_false]
  · simp only [h4, h5, h7, h8, h9, ite_false]
  · rw [h3, Xor.stateAt_writeW_counter, hv, lo32_add, lo32_ext]; rfl
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by rw [h3]; exact c₁)

/-- The destination's window of chunk `t`, and the source's. -/
abbrev win (s₀ : State) (t : Nat) : Region := ⟨dp s₀ + BitVec.ofNat 64 (256 * t), 256⟩
abbrev swin (s₀ : State) (t : Nat) : Region := ⟨srp s₀ + BitVec.ofNat 64 (256 * t), 256⟩

theorem win_sub {s₀ : State} {t : Nat} (h : 256 * t + 256 ≤ L s₀) :
    Region.Sub (win s₀ t) (dR s₀) := Offset.sub_base _ h

theorem swin_sub {s₀ : State} {t : Nat} (h : 256 * t + 256 ≤ L s₀) :
    Region.Sub (swin s₀ t) (srR s₀) := Offset.sub_base _ h

/-- The destination after a chunk, from the source. -/
theorem chunkData {s₀ s : State} {m : Mem} {t : Nat} (h : LInv s₀ t s)
    (hge : 256 * t + 256 ≤ L s₀)
    (hu : ∀ k < 256, m (s.gpr .r7 + BitVec.ofNat 64 k) =
      s.mem (s.gpr .r4 + BitVec.ofNat 64 k) ^^^
      (serialize (block (ctr (stateAt s.mem (s.gpr .r3)) (k / 64)))).getD (k % 64) 0)
    (hf : Frame [⟨s.gpr .r7, 256⟩] s.mem m) : Dst s₀ (256 * (t + 1)) m := by
  intro k hk
  have hL := L_lt s₀
  by_cases hin : 256 * t ≤ k ∧ k < 256 * t + 256
  · have he : s.gpr .r7 + BitVec.ofNat 64 (k - 256 * t) = dp s₀ + BitVec.ofNat 64 k := by
      rw [h.r7, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hin.1]
    have hs : s.gpr .r4 + BitVec.ofNat 64 (k - 256 * t) = srp s₀ + BitVec.ofNat 64 k := by
      rw [h.r4, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hin.1]
    have hh := hu (k - 256 * t) (by omega)
    rw [he, hs, h.src k hk hin.1, h.r3, h.cnt, ← ks_shift (S0 s₀) hk hin.1] at hh
    rw [ite_eq_left (by omega)]; exact hh
  · have hx : ¬ (win s₀ t).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
      simp only [Region.Contains, Nat.add_one_le_iff]
      rw [Offset.lt_iff _ _ (by omega), Mem.sub_ofNat_toNat _ (by omega : k < 2 ^ 64)]
      exact hin
    have hh := hf (dp s₀ + BitVec.ofNat 64 k) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; rw [h.r7]; exact hx)
    rw [hh, h.data k hk]
    by_cases hold : k < 256 * t
    · rw [ite_eq_left hold, ite_eq_left (by omega)]
    · rw [ite_eq_right hold, ite_eq_right (by omega)]

theorem body_ok {s₀ : State} (hp : XPre s₀) {t : Nat}
    (hge : 256 * t + 256 ≤ L s₀) {s : State} (h : LInv s₀ t s) :
    WP isa body s fun s' => LInv s₀ (t + 1) s' ∧
      s'.gpr .r9 = BitVec.ofNat 64 ((L s₀ - 256 * (t + 1)) / 256) := by
  have hL := L_lt s₀
  have hcp : CPre s := by
    refine ⟨h.r10, fun r hr => ?_⟩
    rw [h.rd, h.wr, hp.rd, hp.wr, h.r3]
    exact ⟨stR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hsrc : ∀ r j : Fin 4, InRegions (s.rd ++ s.wr)
      (s.gpr .r4 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro r j; rw [h.rd, h.wr, hp.rd, hp.wr, h.r4, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨srR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hout : ∀ r j : Fin 4, InRegions s.wr
      (s.gpr .r7 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro r j; rw [h.wr, hp.wr, h.r7, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨dR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have halias : s.gpr .r4 = s.gpr .r7 ∨
      (⟨s.gpr .r4, 256⟩ : Region).Disjoint ⟨s.gpr .r7, 256⟩ := by
    rw [h.r4, h.r7]
    rcases hp.alias with he | hd
    · exact .inl (by rw [he])
    · exact .inr ((hd.sub_left (swin_sub hge)).sub_right (win_sub hge))
  apply WP.seq
  refine (chunk_ok s hcp halias hsrc hout).mono fun u ⟨hu, hf, hk⟩ => ?_
  have hcnt : stateAt u.mem (st s₀) = ctr (S0 s₀) (4 * t) := by
    rw [← h.cnt]
    apply Xor.stateAt_frame hf
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    rw [h.r7]; exact hp.st_d.sub_right (win_sub hge)
  have hdata := chunkData h hge hu hf
  have hft : Frame [dR s₀] s.mem u.mem := hf.sub (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    refine ⟨dR s₀, by simp, ?_⟩; rw [h.r7]; exact win_sub hge)
  have hsrc' : Src s₀ (256 * (t + 1)) u.mem := Xor.src_step hp (by omega) h.src hft hdata
  have hk' : ∀ r, r ≠ .r8 → r ≠ .r12 → u.gpr r = s.gpr r := hk.gpr
  have hr3 : u.gpr .r3 = st s₀ := (hk' _ (by decide) (by decide)).trans h.r3
  refine (next_ok hp hr3 (hk.rd.trans h.rd) (hk.wr.trans h.wr)).mono fun v
    ⟨hv4, hv7, hv5, hv9, hkeep, hctr, hframe, hrd, hwr, hsp, hlr, hsy⟩ => ?_
  have hadv : ∀ p : Addr, p + BitVec.ofNat 64 (256 * t) + BitVec.ofNat 64 256 =
      p + BitVec.ofNat 64 (256 * (t + 1)) := by
    intro p
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 256 * t + 256 = 256 * (t + 1) by omega]
  have hrem : v.gpr .r5 = BitVec.ofNat 64 (L s₀ - 256 * (t + 1)) := by
    rw [hv5, hk' _ (by decide) (by decide), h.r5,
      Offset.ofNat_sub_ofNat (by omega), show L s₀ - 256 * t - 256 = L s₀ - 256 * (t + 1) by omega]
  have g : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r7 → r ≠ .r8 → r ≠ .r9 → r ≠ .r12 → v.gpr r = s.gpr r :=
    fun r h4 h5 h7 h8 h9 h12 => (hkeep r h4 h5 h7 h8 h9).trans (hk' r h8 h12)
  refine ⟨⟨by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r3],
    by rw [hv4, hk' _ (by decide) (by decide), h.r4, hadv], hrem,
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r6],
    by rw [hv7, hk' _ (by decide) (by decide), h.r7, hadv],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r10, hsy,
      hk.syms],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r11],
    by omega, fun r hr => ?_, hrd.trans (hk.rd.trans h.rd), hwr.trans (hk.wr.trans h.wr),
    hsp.trans (hk.sp.trans h.sp), ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨h4, h5, h7, h8, h9, -, -, h12⟩ := preserved_ne r hr
    rw [g r h4 h5 h7 h8 h9 h12]; exact h.keep r hr
  · rw [hctr, hcnt, ctr_ctr, show 4 * t + 4 = 4 * (t + 1) by omega]
  · refine hdata.frame hframe ?_
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact hp.st_d.symm
  · refine hsrc'.frame hframe ?_
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact hp.st_s.symm
  · rw [hv9, ← hv5, hrem, shr8 (by omega)]

/-- After the chunks: what `rest_ok` needs, and our caller's registers. -/
structure Done (s₀ : State) (t : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = st s₀
  r4 : s.gpr .r4 = srp s₀ + BitVec.ofNat 64 (256 * t)
  r5 : s.gpr .r5 = BitVec.ofNat 64 (L s₀ - 256 * t)
  r6 : s.gpr .r6 = bp s₀
  r7 : s.gpr .r7 = dp s₀ + BitVec.ofNat 64 (256 * t)
  le : 256 * t ≤ L s₀
  keep : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) (4 * t)
  data : Dst s₀ (256 * t) s.mem
  src : Src s₀ (256 * t) s.mem

theorem exec_adrSym (s : State) :
    exec (.adrSym .r10 tblName) s = some { s.write .r10 (s.syms tblName) with
      lr := s.unknowns 0, unknowns := fun n => s.unknowns (n + 1) } := by
  simp only [reduceExec, ne_eq, reduceCtorEq, not_false_eq_true, ite_true]

theorem bulk_ok {s₀ : State} (hp : XPre s₀) {s : State} (hge : 256 ≤ L s₀)
    (h3 : s.gpr .r3 = st s₀) (h4 : s.gpr .r4 = srp s₀) (h5 : s.gpr .r5 = s₀.gpr .r5)
    (h6 : s.gpr .r6 = bp s₀) (h7 : s.gpr .r7 = dp s₀) (hkeep : ∀ r ∈ preserved, s.gpr r = s₀.gpr r)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hsp : s.sp = s₀.sp) (hlr : s.lr = s₀.lr)
    (hm : s.mem = s₀.mem) :
    WP isa bulk s fun u => ∃ t, L s₀ - 256 * t < 256 ∧ Done s₀ t u := by
  have hL := L_lt s₀
  apply WP.seq
  have h₁ : WP isa (.block [.mflr .r11, .adrSym .r10 tblName]) s fun a => LInv s₀ 0 a := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runBlock_nil, exec_mflr, runStep_some, exec_adrSym, Option.some.injEq,
      exists_eq_left']
    have g : ∀ r, r ≠ .r10 → r ≠ .r11 →
        ({ (s.write .r11 s.lr).write .r10 ((s.write .r11 s.lr).syms tblName) with
          lr := (s.write .r11 s.lr).unknowns 0,
          unknowns := fun n => (s.write .r11 s.lr).unknowns (n + 1) } : State).gpr r = s.gpr r := by
      intro r h10 h11
      simp only [RegUpd.gpr_write_of_ne _ _ h10, RegUpd.gpr_write_of_ne _ _ h11]
    refine ⟨by rw [g _ (by decide) (by decide), h3], by rw [g _ (by decide) (by decide), h4]; simp,
      by rw [g _ (by decide) (by decide), h5]; simp [L], by rw [g _ (by decide) (by decide), h6],
      by rw [g _ (by decide) (by decide), h7]; simp, by simp only [RegUpd.gpr_write_self]; rfl,
      by simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.r11 ≠ .r10 by decide), RegUpd.gpr_write_self, hlr],
      by omega, fun r hr => ?_, hrd, hwr, hsp, ?_, ?_, ?_⟩
    · obtain ⟨-, -, -, -, -, h10, h11, -⟩ := preserved_ne r hr
      rw [g r h10 h11]; exact hkeep r hr
    · simp only [RegUpd.mem_write]; rw [hm]; exact (VG.Proof.ChaCha20.ctr_zero _).symm
    · intro k _; simp only [RegUpd.mem_write, hm, Nat.mul_zero, Nat.not_lt_zero, ite_false]
    · intro k _ _; simp only [RegUpd.mem_write, hm]
  refine h₁.mono fun a ha => ?_
  apply WP.seq
  let Inv : Nat → State → Prop := fun n s =>
    ∃ t, n = L s₀ - 256 * t ∧ 256 ≤ n ∧ LInv s₀ t s
  have hloop : WP isa (.loop body (.nonzero .d .r9)) a fun c =>
      ∃ t, L s₀ - 256 * t < 256 ∧ LInv s₀ t c := by
    refine WP.loop (M := isa) Inv ?_ (L s₀) a ⟨0, by omega, hge, ha⟩
    intro n s ⟨t, hn, hge, hi⟩
    refine (body_ok hp (by omega) hi).mono fun u ⟨hu, h9⟩ => ?_
    have hc := Xor.eval_nonzero_ofNat u .r9
      (by omega : (L s₀ - 256 * (t + 1)) / 256 < 2 ^ 64) h9
    by_cases he : L s₀ - 256 * (t + 1) < 256
    · left
      refine ⟨?_, t + 1, he, hu⟩
      simpa only [Nat.div_eq_of_lt he, ne_eq, not_true_eq_false, decide_false] using hc
    · right
      refine ⟨?_, L s₀ - 256 * (t + 1), by omega, t + 1, rfl, by omega, hu⟩
      have hne : (L s₀ - 256 * (t + 1)) / 256 ≠ 0 := by omega
      simpa only [decide_eq_true hne] using hc
  refine hloop.mono fun c ⟨t, ht, hc⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runBlock_nil, exec_mtlr, runStep_some, Option.some.injEq, exists_eq_left']
  exact ⟨t, ht, hc.r3, hc.r4, hc.r5, hc.r6, hc.r7, hc.le, hc.keep, hc.rd, hc.wr, hc.sp, hc.r11, hc.cnt,
    hc.data, hc.src⟩

theorem correct (s₀ : State) (hs : xorPPC64LE.pre s₀) :
    WP isa Impl.ChaCha20.PPC64LE.Vmx4.xor s₀ fun u => abiPreserved s₀ u ∧ xorPPC64LE.post s₀ u := by
  have hp := XPre.of s₀ hs
  have hL := L_lt s₀
  apply WP.seq
  have h₁ : WP isa (.block [.lsr .d .r9 .r5 8]) s₀ fun s => s = s₀.write .r9 (s₀.gpr .r5 >>> 8) := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runBlock_nil, exec_lsr_d (show 8 < 64 by decide), runStep_some,
      Option.some.injEq, exists_eq_left']
  refine h₁.mono fun s hs₁ => ?_
  subst hs₁
  have g : ∀ r, r ≠ .r9 → (s₀.write .r9 (s₀.gpr .r5 >>> 8)).gpr r = s₀.gpr r :=
    fun r h => RegUpd.gpr_write_of_ne _ _ h
  have h9 : (s₀.write .r9 (s₀.gpr .r5 >>> 8)).gpr .r9 = BitVec.ofNat 64 (L s₀ / 256) := by
    rw [RegUpd.gpr_write_self, ← shr8 hL]
    simp [L]
  apply WP.seq
  have hmid : WP isa (.ite (.zero .d .r9) (.block []) bulk) (s₀.write .r9 (s₀.gpr .r5 >>> 8))
      fun u => ∃ t, Done s₀ t u := by
    refine WP.ite (decide (L s₀ < 256)) ?_ (fun hb => WP.block_nil ⟨0, ?_⟩) (fun hb => ?_)
    · rw [Xor.eval_zero, h9, Xor.ofNat_beq_zero (by omega)]
      congr 2; apply propext; omega
    · refine ⟨by rw [g _ (by decide)], by rw [g _ (by decide)]; simp, by rw [g _ (by decide)]; simp [L],
        by rw [g _ (by decide)], by rw [g _ (by decide)]; simp, by omega,
        fun r hr => g r (by obtain ⟨-, -, -, -, h, -⟩ := preserved_ne r hr; exact h), rfl, rfl, rfl, rfl,
        ?_, ?_, ?_⟩
      · exact (VG.Proof.ChaCha20.ctr_zero _).symm
      · intro k _; simp only [RegUpd.mem_write, Nat.mul_zero, Nat.not_lt_zero, ite_false]
      · intro k _ _; rfl
    · have hge : 256 ≤ L s₀ := by have := of_decide_eq_false hb; omega
      refine (bulk_ok hp hge (g _ (by decide)) (g _ (by decide)) (g _ (by decide)) (g _ (by decide))
        (g _ (by decide)) (fun r hr => g r (by obtain ⟨-, -, -, -, h, -⟩ := preserved_ne r hr; exact h))
        rfl rfl rfl rfl rfl).mono fun u ⟨t, _, hu⟩ => ⟨t, hu⟩
  refine hmid.mono fun u ⟨t, hu⟩ => ?_
  refine (rest_ok hp hu.le (by omega) hu.r3 hu.r4 hu.r5 hu.r6 hu.r7 hu.rd hu.wr
    (by rw [hu.cnt, show 256 * t / 64 = 4 * t by omega]) hu.data hu.src).mono fun v ⟨ha, hpost⟩ => ?_
  exact ⟨⟨fun r hr => (ha.1 r hr).trans (hu.keep r hr), ha.2.1.trans hu.sp, ha.2.2.trans hu.lr⟩, hpost⟩

theorem xor_correct (s : State) (hs : xorPPC64LE.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.PPC64LE.Vmx4.xor s t s' ∧ abiPreserved s s' ∧ xorPPC64LE.post s s' :=
  correct s hs

/-! ## Constant time -/

theorem xor_ct : ConstantTime isa xorPPC64LE.pre xorPPC64LE.pub Impl.ChaCha20.PPC64LE.Vmx4.xor :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => Xor.agree₀ hp) (by taint_decide)

/-! ## Calling it

What a caller of `vg_chacha20_xor` needs, once for every caller: a call from
`src` to `dst` (`xor_call_to`), and in place (`xor_call`). -/

theorem xor_noFrames : Impl.ChaCha20.PPC64LE.Vmx4.xor.noFrames = true := by decide +kernel

theorem xor_call_to {s : State} {S X D B : Addr} {n : Nat} (h3 : s.gpr .r3 = S) (h4 : s.gpr .r4 = X)
    (h5 : s.gpr .r5 = BitVec.ofNat 64 n) (h6 : s.gpr .r6 = B) (h7 : s.gpr .r7 = D) (hn : n < 2 ^ 64)
    (hSX : (⟨S, 64⟩ : Region).Disjoint ⟨X, n⟩) (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩)
    (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩) (hXB : (⟨X, n⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hXD : D = X ∨ (⟨X, n⟩ : Region).Disjoint ⟨D, n⟩)
    (hX : X.toNat + n ≤ 2 ^ 64) (hD : D.toNat + n ≤ 2 ^ 64)
    (hc : Covers ([⟨X, n⟩] ++ [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.mem s'.mem → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (∀ r, r ∉ linkRegs → (∀ i ∈ instrs Impl.ChaCha20.PPC64LE.Vmx4.xor, dstOf i ≠ some r) →
        s'.gpr r = s.gpr r) →
      bytesAt s'.mem D n = List.zipWith (· ^^^ ·) (bytesAt s.mem X n) (keystream (stateAt s.mem S) n) →
      Q s') :
    WP isa (.call "vg_chacha20_xor" Impl.ChaCha20.PPC64LE.Vmx4.xor) s Q := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have c3 : s.callEntry.gpr .r3 = S := (State.callEntry_gpr _ (by decide)).trans h3
  have c4 : s.callEntry.gpr .r4 = X := (State.callEntry_gpr _ (by decide)).trans h4
  have c5 : s.callEntry.gpr .r5 = BitVec.ofNat 64 n := (State.callEntry_gpr _ (by decide)).trans h5
  have c6 : s.callEntry.gpr .r6 = B := (State.callEntry_gpr _ (by decide)).trans h6
  have c7 : s.callEntry.gpr .r7 = D := (State.callEntry_gpr _ (by decide)).trans h7
  refine WP.call (k := Proof.ChaCha20.xorPPC64LE) xor_correct
    (rd := [⟨X, n⟩]) (wr := [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) ?_ hc hw ?_ xor_noFrames
  · simp only [Proof.ChaCha20.xorPPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c3, c4, c5, c6, c7, hn']
    exact ⟨trivial, trivial, hSX, hSD, hSB, hXB, hDB, hXD, hX, hD⟩
  · intro s' hrd hwr hsp hf hcs hk hpost
    simp only [Proof.ChaCha20.xorPPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c3, c4, c5, c7, hn'] at hpost
    exact hQ s' hrd hwr hsp hf hcs hk hpost

/-- In place: `xor_call_to` with `dst = src`, whose region the caller may
write. -/
theorem xor_call {s : State} {S D B : Addr} {n : Nat} (h3 : s.gpr .r3 = S) (h4 : s.gpr .r4 = D)
    (h5 : s.gpr .r5 = BitVec.ofNat 64 n) (h6 : s.gpr .r6 = B) (h7 : s.gpr .r7 = D) (hn : n < 2 ^ 64)
    (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩) (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hD : D.toNat + n ≤ 2 ^ 64)
    (hc : Covers ([] ++ [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.mem s'.mem → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (∀ r, r ∉ linkRegs → (∀ i ∈ instrs Impl.ChaCha20.PPC64LE.Vmx4.xor, dstOf i ≠ some r) →
        s'.gpr r = s.gpr r) →
      bytesAt s'.mem D n = List.zipWith (· ^^^ ·) (bytesAt s.mem D n) (keystream (stateAt s.mem S) n) →
      Q s') :
    WP isa (.call "vg_chacha20_xor" Impl.ChaCha20.PPC64LE.Vmx4.xor) s Q := by
  refine xor_call_to h3 h4 h5 h6 h7 hn hSD hSD hSB hDB hDB (.inl rfl) hD hD ?_ hw hQ
  intro a m ⟨r, hr, hcr⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | hr
  · exact hc a m ⟨⟨D, n⟩, by simp, hcr⟩
  · exact hc a m ⟨r, by simpa using hr, hcr⟩


end VG.Proof.ChaCha20.PPC64LE.Vmx4
