module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndScan
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: the call's arguments

With `PS` full after `i` octets (`Ready`): `tape` is `[i, 0]`, and the
arguments of `vg_rsa_pkcs1_encrypt_precomputed` in registers and at `sp`
(`args_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Random

/-- `PS` full after `i` octets, its octets `ps`. -/
structure Ready (s u : State) (i : Nat) (pad : List Byte) : Prop extends InFrame s u where
  keep : Keeps [.x9, .x11, .x12, .x14, .x15, .x16, .x17] s u
  x12 : u.gpr .x12 = BitVec.ofNat 64 ((stackArg s 2).toNat - i)
  x15 : u.gpr .x15 = BitVec.ofNat 64 (psLen s)
  len : pad.length = psLen s
  buf : Spec.Rsa.bytesAt u.mem (off (Q s) oBuf) (psLen s) = pad
  used : i ≤ (stackArg s 2).toNat

/-- The callee's stack arguments. -/
def callArg (s : State) : Nat → Addr
  | 0 => off (Q s) oBuf
  | 1 => BitVec.ofNat 64 (psLen s)
  | 2 => stackArg s 3
  | 3 => stackArg s 4
  | 4 => stackArg s 5
  | _ => stackArg s 6

/-- After the call's arguments. -/
structure Args (s w : State) (i : Nat) (pad : List Byte) : Prop where
  sp : w.sp = Q s
  rd : w.rd = s.rd
  wr : w.wr = (entered s).wr
  v : w.v = s.v
  fr : Frame [⟨Q s, 1104⟩, tapeR s] s.mem w.mem
  ps : w.mem.readW (off (Q s) oPs) 64 = BitVec.ofNat 64 (psLen s)
  lr : w.mem.readW (off (Q s) 1088) 64 = s.gpr .x30
  args : ∀ j < 6, w.mem.readW (off (Q s) (8 * j)) 64 = callArg s j
  buf : Spec.Rsa.bytesAt w.mem (off (Q s) oBuf) (psLen s) = pad
  len : pad.length = psLen s
  tape0 : w.mem.readW (s.gpr .x2) 64 = BitVec.ofNat 64 i
  tape1 : w.mem.readW (s.gpr .x2 + BitVec.ofNat 64 8) 64 = 0
  x0 : w.gpr .x0 = s.gpr .x0
  x1 : w.gpr .x1 = s.gpr .x1
  x2 : w.gpr .x2 = s.gpr .x3
  x3 : w.gpr .x3 = s.gpr .x4
  x4 : w.gpr .x4 = s.gpr .x5
  x5 : w.gpr .x5 = s.gpr .x6
  x6 : w.gpr .x6 = s.gpr .x7
  x7 : w.gpr .x7 = stackArg s 0
  keep : Keeps [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s w

/-- A stack argument, in a frame's memory. -/
theorem arg_u {P : Nat} {s u : State} (hp : RPre P s) (hf : InFrame s u) {j : Nat} (hj : j < 7) :
    u.mem.read (Q s + BitVec.ofNat 64 (1104 + 8 * j)) 8 = stackArg s j := by
  have hQ := Q_toNat hp
  have h := hf.fr.read (r := ⟨Q s + BitVec.ofNat 64 (1104 + 8 * j), 8⟩) (Region.contains_self _ _)
    (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint_base (Q s) (d := 1104 + 8 * j) (n := 8) (k := 1104) (by omega) (by omega)) (by decide)
  rw [h]
  have := arg_read s hj
  rw [entered_mem] at this
  rw [← this, Mem.writeW, Mem.read_write_sep (Offset.sep _ (.inr (by omega)) (by omega) (by omega)) (by decide)]

/-- The memory after the call's arguments. -/
def argMem (s u : State) : Mem :=
  (((((((u.mem.write (u.gpr .x2 + 0#64) 8 (stackArg s 2 - u.gpr .x12)).write (u.gpr .x2 + 8#64) 8
    (BitVec.setWidth 64 (0 : BitVec 16) <<< 0)).write (Q s + 0#64) 8 (Q s + 64#64)).write (Q s + 8#64) 8
    (u.gpr .x15)).write (Q s + 16#64) 8 (stackArg s 3)).write (Q s + 24#64) 8 (stackArg s 4)).write
    (Q s + 32#64) 8 (stackArg s 5)).write (Q s + 40#64) 8 (stackArg s 6)

theorem rd_self (m : Mem) (a : Addr) (v : BitVec 64) : (m.write a 8 v).readW a 64 = v := by
  have := Mem.readW_writeW_self m a 8 v (by decide)
  simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq] at this
  exact this

theorem rd_sep {m : Mem} {a b : Addr} (v : BitVec 64) (h : Mem.Sep a 8 b 8) : (m.write b 8 v).readW a 64 = m.readW a 64 :=
  Bytes.readW_write_sep h (by decide)

theorem rd_q (m : Mem) (q : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2 ^ 64)
    (he : e + 8 ≤ 2 ^ 64) :
    (m.write (q + BitVec.ofNat 64 e) 8 v).readW (q + BitVec.ofNat 64 d) 64 = m.readW (q + BitVec.ofNat 64 d) 64 :=
  rd_sep v (Offset.sep q h hd he)

theorem sub_used {n i : Nat} (hn : n < 2 ^ 64) (hi : i ≤ n) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 (n - i) = BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show n - i < 2 ^ 64 by omega), Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
    show 2 ^ 64 - (n - i) + n = i + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- What the arguments write: the tape and the callee's stack arguments. -/
theorem argMem_frame {P : Nat} {s u : State} (hp : RPre P s) (hx2 : u.gpr .x2 = s.gpr .x2) :
    Frame [tapeR s, ⟨Q s, 48⟩] u.mem (argMem s u) := by
  have hQ := Q_toNat hp
  have hc : ∀ {d : Nat}, d + 8 ≤ 48 → (⟨Q s, 48⟩ : Region).Contains (Q s + BitVec.ofNat 64 d) 8 :=
    fun hd => Offset.contains_base _ hd (by omega)
  have ht : ∀ {d : Nat}, d + 8 ≤ 16 → (tapeR s).Contains (u.gpr .x2 + BitVec.ofNat 64 d) 8 :=
    fun hd => by rw [hx2]; exact Offset.contains_base _ hd (by omega)
  have q : (⟨Q s, 48⟩ : Region) ∈ [tapeR s, ⟨Q s, 48⟩] := by simp
  have t : tapeR s ∈ [tapeR s, ⟨Q s, 48⟩] := by simp
  exact ((((((((Frame.refl _ _).write t _ (ht (d := 0) (by decide))).write t _ (ht (d := 8) (by decide))).write q _
    (hc (d := 0) (by decide))).write q _ (hc (d := 8) (by decide))).write q _ (hc (d := 16) (by decide))).write q _
    (hc (d := 24) (by decide))).write q _ (hc (d := 32) (by decide))).write q _ (hc (d := 40) (by decide))

theorem argMem_slot (s u : State) {j : Nat} (hj : j < 6) :
    (argMem s u).readW (off (Q s) (8 * j)) 64 =
      [Q s + 64#64, u.gpr .x15, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6].getD j 0 := by
  match j, hj with
  | 0, _ => simp (disch := decide) only [argMem, off, rd_q, rd_self, Nat.reduceMul]; rfl
  | 1, _ => simp (disch := decide) only [argMem, off, rd_q, rd_self, Nat.reduceMul]; rfl
  | 2, _ => simp (disch := decide) only [argMem, off, rd_q, rd_self, Nat.reduceMul]; rfl
  | 3, _ => simp (disch := decide) only [argMem, off, rd_q, rd_self, Nat.reduceMul]; rfl
  | 4, _ => simp (disch := decide) only [argMem, off, rd_q, rd_self, Nat.reduceMul]; rfl
  | 5, _ => simp (disch := decide) only [argMem, off, rd_self, Nat.reduceMul]; rfl

theorem argMem_tape {P : Nat} {s u : State} (hp : RPre P s) (hx2 : u.gpr .x2 = s.gpr .x2) :
    (argMem s u).readW (s.gpr .x2) 64 = stackArg s 2 - u.gpr .x12 ∧
      (argMem s u).readW (s.gpr .x2 + BitVec.ofNat 64 8) 64 = 0 := by
  have hQ := Q_toNat hp
  have hw := hp.wT
  have hd : (tapeR s).Disjoint ⟨Q s, 48⟩ := fun x h₁ h₂ =>
    hp.dKt x (frame_sub (P := P) s (d := 0) (n := 48) (by decide) x (by rw [off, add_zero']; exact h₂)) h₁
  have hsep : ∀ {a : Nat}, a + 8 ≤ 16 → ∀ {d : Nat}, d + 8 ≤ 48 →
      Mem.Sep (s.gpr .x2 + BitVec.ofNat 64 a) 8 (Q s + BitVec.ofNat 64 d) 8 := fun ha _ hd' =>
    hd.sep (Offset.contains_base _ ha (by omega)) (Offset.contains_base _ hd' (by omega))
  have e0 : s.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 0 := (add_zero' _).symm
  constructor
  · rw [e0]
    simp only [argMem, hx2]
    rw [rd_sep _ (hsep (a := 0) (by decide) (d := 40) (by decide)), rd_sep _ (hsep (a := 0) (by decide) (d := 32) (by decide)),
      rd_sep _ (hsep (a := 0) (by decide) (d := 24) (by decide)), rd_sep _ (hsep (a := 0) (by decide) (d := 16) (by decide)),
      rd_sep _ (hsep (a := 0) (by decide) (d := 8) (by decide)), rd_sep _ (hsep (a := 0) (by decide) (d := 0) (by decide)),
      rd_q _ _ _ (.inl (by decide)) (by decide) (by decide), rd_self]
  · simp only [argMem, hx2]
    rw [rd_sep _ (hsep (a := 8) (by decide) (d := 40) (by decide)), rd_sep _ (hsep (a := 8) (by decide) (d := 32) (by decide)),
      rd_sep _ (hsep (a := 8) (by decide) (d := 24) (by decide)), rd_sep _ (hsep (a := 8) (by decide) (d := 16) (by decide)),
      rd_sep _ (hsep (a := 8) (by decide) (d := 8) (by decide)), rd_sep _ (hsep (a := 8) (by decide) (d := 0) (by decide)),
      rd_self]
    rfl

theorem args_ok {P : Nat} {s u : State} (hp : RPre P s) {i : Nat} {pad : List Byte} (h : Ready s u i pad) :
    WP isa (.block callArgs) u (Args s · i pad) := by
  have hQ := Q_toNat hp
  have hsp := h.sp
  have hin : ∀ {j : Nat}, j < 7 → InRegions (u.rd ++ u.wr) (Q s + BitVec.ofNat 64 (1104 + 8 * j)) 8 :=
    fun hj => by rw [h.rd, h.wr, ← entered_rd]; exact args_in hp hj
  have a0 : InRegions (u.rd ++ u.wr) (Q s + BitVec.ofNat 64 1104) 8 := hin (j := 0) (by decide)
  have a2 : InRegions (u.rd ++ u.wr) (Q s + BitVec.ofNat 64 1120) 8 := hin (j := 2) (by decide)
  have a3 : InRegions (u.rd ++ u.wr) (Q s + BitVec.ofNat 64 1128) 8 := hin (j := 3) (by decide)
  have a4 : InRegions (u.rd ++ u.wr) (Q s + BitVec.ofNat 64 1136) 8 := hin (j := 4) (by decide)
  have a5 : InRegions (u.rd ++ u.wr) (Q s + BitVec.ofNat 64 1144) 8 := hin (j := 5) (by decide)
  have a6 : InRegions (u.rd ++ u.wr) (Q s + BitVec.ofNat 64 1152) 8 := hin (j := 6) (by decide)
  have m0 : u.mem.read (Q s + BitVec.ofNat 64 1104) 8 = stackArg s 0 := arg_u hp h.toInFrame (j := 0) (by decide)
  have m2 : u.mem.read (Q s + BitVec.ofNat 64 1120) 8 = stackArg s 2 := arg_u hp h.toInFrame (j := 2) (by decide)
  have m3 : u.mem.read (Q s + BitVec.ofNat 64 1128) 8 = stackArg s 3 := arg_u hp h.toInFrame (j := 3) (by decide)
  have m4 : u.mem.read (Q s + BitVec.ofNat 64 1136) 8 = stackArg s 4 := arg_u hp h.toInFrame (j := 4) (by decide)
  have m5 : u.mem.read (Q s + BitVec.ofNat 64 1144) 8 = stackArg s 5 := arg_u hp h.toInFrame (j := 5) (by decide)
  have m6 : u.mem.read (Q s + BitVec.ofNat 64 1152) 8 = stackArg s 6 := arg_u hp h.toInFrame (j := 6) (by decide)
  have hx2 : u.gpr .x2 = s.gpr .x2 := h.keep _ (by decide)
  have htw : (tapeR s) ∈ u.wr := by rw [h.wr, entered_wr, hp.hwr]; simp
  have t0 : InRegions u.wr (u.gpr .x2 + 0#64) 8 :=
    ⟨tapeR s, htw, by rw [hx2]; exact Offset.contains_base _ (by decide) (by decide)⟩
  have t8 : InRegions u.wr (u.gpr .x2 + 8#64) 8 :=
    ⟨tapeR s, htw, by rw [hx2]; exact Offset.contains_base _ (by decide) (by decide)⟩
  have hfw : ∀ {d : Nat}, d + 8 ≤ frameBytes → InRegions u.wr (Q s + BitVec.ofNat 64 d) 8 :=
    fun hd => by rw [h.wr]; exact frame_in hd
  have s0 : InRegions u.wr (Q s + 0#64) 8 := hfw (d := 0) (by decide)
  have s8 : InRegions u.wr (Q s + 8#64) 8 := hfw (d := 8) (by decide)
  have s16 : InRegions u.wr (Q s + 16#64) 8 := hfw (d := 16) (by decide)
  have s24 : InRegions u.wr (Q s + 24#64) 8 := hfw (d := 24) (by decide)
  have s32 : InRegions u.wr (Q s + 32#64) 8 := hfw (d := 32) (by decide)
  have s40 : InRegions u.wr (Q s + 40#64) 8 := hfw (d := 40) (by decide)
  apply WP.of_runBlock
  simp only [callArgs, Size.bytes, t0, t8, s0, s8, s16, s24, s32, s40, arg, frameBytes, oBuf, runBlock_cons, runStep_some, runBlock_nil, reduceExec, addr,
    State.load, State.store, State.read, Size.bits, BitVec.setWidth_eq, Option.map_some, Option.bind_some,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, ite_true, hsp,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq,
    ite_false, a0, a2, a3, a4, a5, a6, m0, m2, m3, m4, m5, m6, Option.some.injEq, exists_eq_left']
  have hx12 := h.x12
  have hl := (stackArg s 2).isLt
  have hu := h.used
  have hfa := argMem_frame hp hx2
  have hQ' := hQ
  have hP := hp.ps
  have dT : (tapeR s).Disjoint ⟨Q s, 1104⟩ := fun x h₁ h₂ =>
    hp.dKt x (frame_sub (P := P) s (d := 0) (n := 1104) (by decide) x (by rw [off, add_zero']; exact h₂)) h₁
  have apart : ∀ {d n : Nat}, 48 ≤ d → d + n ≤ 1104 → ∀ r ∈ [tapeR s, (⟨Q s, 48⟩ : Region)],
      Region.Disjoint ⟨off (Q s) d, n⟩ r := fun h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (dT.sub_right (Offset.sub_base _ h2)).symm
    · exact Offset.disjoint_base _ h1 (by omega)
  obtain ⟨ht0, ht1⟩ := argMem_tape hp hx2 (u := u)
  have keepS : ∀ r, r ∉ [Reg.x9, .x11, .x12, .x14, .x15, .x16, .x17] → u.gpr r = s.gpr r := h.keep
  refine ⟨rfl, h.rd, h.wr, h.v, ?_, ?_, ?_, fun j hj => ?_, ?_, h.len, ?_, ht1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r hr => ?_⟩
  · exact (h.fr.mono (by simp)).trans (hfa.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨tapeR s, by simp, fun _ h => h⟩
      · exact ⟨⟨Q s, 1104⟩, by simp, by
          have := Offset.sub_base (Q s) (d := 0) (n := 48) (k := 1104) (by decide)
          rwa [add_zero'] at this⟩)
  · show (argMem s u).readW _ 64 = _
    rw [hfa.readW (Region.contains_self _ _) (apart (d := oPs) (n := 8) (by decide) (by decide)) (by decide)]
    exact h.ps
  · show (argMem s u).readW _ 64 = _
    rw [hfa.readW (Region.contains_self _ _) (apart (d := 1088) (n := 8) (by decide) (by decide)) (by decide)]
    exact h.lr
  · show (argMem s u).readW _ 64 = _
    rw [argMem_slot s u hj]
    match j, hj with
    | 0, _ => rfl
    | 1, _ => exact h.x15
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
  · show Spec.Rsa.bytesAt (argMem s u) _ _ = _
    rw [← h.buf]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun j hj => ?_
    exact hfa.bytes (R := ⟨off (Q s) oBuf, psLen s⟩) (apart (by decide) (by unfold oBuf; omega))
      (by show psLen s ≤ 2 ^ 64; omega) (List.mem_range.mp hj)
  · show (argMem s u).readW _ 64 = _
    rw [ht0, hx12, ← sub_used hl hu, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  all_goals simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, BitVec.or_self]
  · exact keepS _ (by decide)
  · exact keepS _ (by decide)
  · exact keepS _ (by decide)
  · exact keepS _ (by decide)
  · exact keepS _ (by decide)
  · exact keepS _ (by decide)
  · exact keepS _ (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := hr
    simp only [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h13, h14, h16, h17, ite_false]
    exact keepS r (by simp [h9, h11, h12, h14, h15, h16, h17])

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd
