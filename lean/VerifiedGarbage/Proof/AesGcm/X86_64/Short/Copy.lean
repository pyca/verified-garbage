import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Impl.AesGcm.X86_64.Short
import VerifiedGarbage.Proof.Framework.X86_64.Avx512

/-!
# AES-GCM's short path on x86-64: copying bytes

Untrusted: everything here is checked by Lean. `copyBytes` copies `rcx`
bytes from `rsi` to `rdi`, 16 at a time through `xmm4` and then one at a
time (`copyBytes_ok`); the buffers do not overlap.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)

/-- The vector registers other than `rs` keep their lanes. -/
def ZKeep (rs : List XReg) (s s' : State) : Prop := ∀ r, r ∉ rs → ∀ l < 4, s'.zlane r l = s.zlane r l

theorem ZKeep.refl (rs : List XReg) (s : State) : ZKeep rs s s := fun _ _ _ _ => rfl

theorem ZKeep.trans {rs : List XReg} {s s' s'' : State} (h : ZKeep rs s s') (h' : ZKeep rs s' s'') :
    ZKeep rs s s'' := fun r hr l hl => by rw [h' r hr l hl, h r hr l hl]

theorem ZKeep.mono {rs rs' : List XReg} {s s' : State} (h : ZKeep rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    ZKeep rs' s s' := fun r hr l hl => h r (fun h' => hr (hs r h')) l hl

theorem zlane_setReg (s : State) (r : Reg) (v : BitVec 64) (x : XReg) (l : Nat) :
    (s.setReg r v).zlane x l = s.zlane x l := rfl

theorem zlane_arithFlags (s : State) {w : Nat} (v : BitVec w) (c o : Bool) (x : XReg) (l : Nat) :
    (arithFlags s v c o).zlane x l = s.zlane x l := rfl

/-- A 16-byte store of a 16-byte load is a write of the bytes loaded. -/
theorem writeW_readW128 (m src : Mem) (a b : Addr) :
    m.writeW a (src.readW b 128) = writeBytes m a (bytesAt src b 16) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (BitVec.setWidth (8 * (128 / 8)) (BitVec.setWidth 128 (src.read b (128 / 8)))) =
    src.read b 16 from by simp]
  rw [write_eq_writeBytes]
  congr 1
  simp only [bytesAt]
  refine List.map_congr_left fun j hj => ?_
  exact Mem.extractLsb'_read src b (List.mem_range.mp hj)

/-- The 16-byte loop's body. -/
abbrev copy16Body : List Instr :=
  [.vmovdquLoad .l128 .xmm4 srcB, .vmovdquStore .l128 dstB .xmm4, .alu .add .r10 (imm 16),
    .alu .cmp .r10 (.reg .r8)]

theorem copy16Step_ok (s : State) {S D : Addr} {i k : Nat} (hs : s.gpr .rsi = S) (hd : s.gpr .rdi = D)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (hk : s.gpr .r8 = BitVec.ofNat 64 k)
    (r : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 16) (w : InRegions s.wr (D + BitVec.ofNat 64 i) 16) :
    ∃ s', runBlock isa copy16Body s = some s' ∧
      s'.mem = writeBytes s.mem (D + BitVec.ofNat 64 i) (bytesAt s.mem (S + BitVec.ofNat 64 i) 16) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 16 ∧
      s'.zf = some (BitVec.ofNat 64 i + 16 - BitVec.ofNat 64 k == 0) ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ZKeep [.xmm4] s s' := by
  have e₁ := ea_idx s .rsi hs hi
  have e₂ := ea_idx s .rdi hd hi
  refine ⟨_, by
    simp only [copy16Body, srcB, dstB, imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, State.load128, State.store128, State.ea, e₁, r, ite_true, Option.map_some, Option.bind_some]
    simp only [State.setV, ite_true, e₂, w]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    exact writeW_readW128 _ _ _ _
  · simp [gpr_setReg, gpr_arithFlags, hi]
  · simp [gpr_setReg, gpr_arithFlags, zf_arithFlags, hi, hk]
  · intro r h₁; simp [gpr_setReg, gpr_arithFlags, h₁]
  · intro r hr l hl
    simp only [List.mem_singleton] at hr
    exact (State.zlane_setV128 s .xmm4 r _ 0 hl).trans (by simp [hr])

/-- `copyStep_ok`, keeping the vector registers. -/
theorem copyStepZ_ok (s : State) {S D : Addr} {i n : Nat} (hs : s.gpr .rsi = S) (hd : s.gpr .rdi = D)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (hn : s.gpr .rcx = BitVec.ofNat 64 n)
    (r : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (D + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa copyBody s = some s' ∧
      s'.mem = s.mem.writeW (D + BitVec.ofNat 64 i) (s.mem (S + BitVec.ofNat 64 i)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 1 ∧
      s'.zf = some (BitVec.ofNat 64 i + 1 - BitVec.ofNat 64 n == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ZKeep [] s s' := by
  have e₁ := ea_idx s .rsi hs hi
  have e₂ := ea_idx s .rdi hd hi
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, ↓reduceDIte, Nat.reduceLT, Nat.reduceGT, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow, BitVec.reduceEq, not_false_eq_true, not_true_eq_false, Bool.not_true, Bool.not_false, and_self, false_implies, implies_true, Nat.reduceBEq, Nat.reduceBNe, decide_true, decide_false, BitVec.reduceSignExtend, copyBody, srcB, dstB, imm, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, execAlu, State.load8, State.store8, State.ea, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false,
      e₁, e₂, r, w]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, fun _ _ _ _ => rfl⟩
  · simp only [mem_setReg, mem_arithFlags, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide),
      BitVec.setWidth_eq]
  · simp [gpr_setReg, hi]
  · simp [hi, hn]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]

theorem shl_ofNat {a k : Nat} (h : a * 2 ^ k < 2 ^ 64) :
    BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (a * 2 ^ k) := by
  have ha : a < 2 ^ 64 := by
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    calc a = a * 1 := (Nat.mul_one a).symm
      _ ≤ a * 2 ^ k := Nat.mul_le_mul_left a this
      _ < 2 ^ 64 := h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.shiftLeft_eq]

/-- What `copyBytes` needs: `n` bytes to read at `S` and to write at `D`, apart. -/
structure CopyPre (s : State) (S D : Addr) (n : Nat) : Prop where
  rsi : s.gpr .rsi = S
  rdi : s.gpr .rdi = D
  rcx : s.gpr .rcx = BitVec.ofNat 64 n
  lt : n < 2 ^ 63
  rd : Covers [⟨S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, n⟩] s.wr
  disj : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩

/-- What `copyBytes` leaves. -/
def CopyPost (s : State) (S D : Addr) (n : Nat) (s' : State) : Prop :=
  s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
    (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
    ZKeep [.xmm4] s s'

theorem in_of_covers16 {rs : List Region} {p : Addr} {n i : Nat} (h : Covers [⟨p, n⟩] rs) (hi : i + 16 ≤ n)
    (hn : n < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 i) 16 :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base p hi (by omega)⟩

/-- The setup: `r10 = 0` and `r8 = 16 ⌊n / 16⌋`. -/
theorem copySetup_ok (s : State) {n : Nat} (hn : s.gpr .rcx = BitVec.ofNat 64 n) (hlt : n < 2 ^ 63) :
    WP isa (.block [.mov32 .r10 (imm 0), .mov .r8 (.reg .rcx), .shift .shr .r8 4, .shift .shl .r8 4,
        .alu .cmp .r8 (imm 0)]) s fun s' =>
      s'.gpr .r10 = BitVec.ofNat 64 0 ∧ s'.gpr .r8 = BitVec.ofNat 64 (16 * (n / 16)) ∧
      s'.zf = some (decide (16 * (n / 16) = 0)) ∧
      (∀ r, r ≠ .r8 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ZKeep [] s s' := by
  have e₁ : BitVec.ofNat 64 n >>> 4 = BitVec.ofNat 64 (n / 16) := shr4 n (by omega)
  have e₂ : BitVec.ofNat 64 (n / 16) <<< 4 = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [shl_ofNat (by omega)]; congr 1; omega
  apply WP.of_runBlock
  refine ⟨_, by xrun [execShift, hn, e₁, e₂], ?_⟩
  refine ⟨by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags], by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags],
    ?_, fun r h₁ h₂ => by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, h₁, h₂], rfl, rfl, rfl,
    fun _ _ _ _ => rfl⟩
  simp only [zf_arithFlags]
  rw [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, sub_beq (by omega) (by decide)]

theorem copyBytes_ok (s : State) {S D : Addr} {n : Nat} (h : CopyPre s S D n) :
    WP isa copyBytes s (CopyPost s S D n) := by
  have hn63 := h.lt
  refine WP.seq (WP.mono (copySetup_ok s h.rcx h.lt) fun s₁ ⟨r10₁, r8₁, zf₁, g₁, m₁, rd₁, wr₁, z₁⟩ => ?_)
  -- After the 16-byte loop: the first `16 ⌊n / 16⌋` bytes copied.
  let q := n / 16
  have mid : WP isa (.ite .e (.block []) (.loop (.block copy16Body) .ne)) s₁ fun t =>
      t.gpr .r10 = BitVec.ofNat 64 (16 * q) ∧ t.mem = writeBytes s.mem D (bytesAt s.mem S (16 * q)) ∧
      (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      ZKeep [.xmm4] s t := by
    refine WP.ite (decide (16 * q = 0)) (by simp only [eval, zf₁, q]) (fun hz => ?_) (fun hz => ?_)
    · have hq : 16 * q = 0 := of_decide_eq_true hz
      refine WP.block_nil ⟨by rw [r10₁, hq], by rw [m₁, hq]; simp [bytesAt, writeBytes_nil],
        fun r a b c => g₁ r b c, rd₁, wr₁, z₁.mono (by simp)⟩
    · have hq : 0 < q := by have := of_decide_eq_false hz; omega
      refine WP.loop (M := isa) (body := .block copy16Body) (c := .ne)
        (fun (k : Nat) (t : State) => ∃ j, k = q - j ∧ j < q ∧ t.gpr .r10 = BitVec.ofNat 64 (16 * j) ∧
          t.mem = writeBytes s.mem D (bytesAt s.mem S (16 * j)) ∧
          (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → t.gpr r = s.gpr r) ∧
          t.gpr .r8 = BitVec.ofNat 64 (16 * q) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ ZKeep [.xmm4] s t) ?_ (q - 0) _
        ⟨0, rfl, hq, by rw [r10₁], by rw [m₁]; simp [bytesAt, writeBytes_nil], fun r a b c => g₁ r b c,
          r8₁, rd₁, wr₁, z₁.mono (by simp)⟩
      rintro k t ⟨j, rfl, hj, r10, mem, g, r8, rd, wr, z⟩
      have hj16 : 16 * j + 16 ≤ n := by omega
      obtain ⟨t', run', mem', r10', zf', g', rd', wr', z'⟩ := copy16Step_ok t
        (by rw [g _ (by decide) (by decide) (by decide), h.rsi])
        (by rw [g _ (by decide) (by decide) (by decide), h.rdi]) r10 r8
        (by rw [rd, wr]; exact in_of_covers16 h.rd hj16 (by omega))
        (by rw [wr]; exact in_of_covers16 h.wr hj16 (by omega))
      refine WP.of_runBlock ⟨t', run', ?_⟩
      have hlen : (bytesAt s.mem S (16 * j)).length = 16 * j := length_bytesAt _ _ _
      have hsrc : bytesAt t.mem (S + BitVec.ofNat 64 (16 * j)) 16 = bytesAt s.mem (S + BitVec.ofNat 64 (16 * j)) 16 := by
        rw [mem]
        refine bytesAt_frame (writeBytes_frame' s.mem hlen) (fun r hr => ?_) (by decide)
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.disj.sub_left (Offset.sub_base S hj16)).sub_right (Region.sub_prefix (by omega))
      have hmem : t'.mem = writeBytes s.mem D (bytesAt s.mem S (16 * (j + 1))) := by
        rw [mem', hsrc, mem, show 16 * (j + 1) = 16 * j + 16 by omega, bytesAt_add]
        conv => lhs; rw [show D + BitVec.ofNat 64 (16 * j) = D + BitVec.ofNat 64 (bytesAt s.mem S (16 * j)).length
          by rw [hlen]]
        exact writeBytes_append s.mem D (bytesAt s.mem S (16 * j)) (bytesAt s.mem (S + BitVec.ofNat 64 (16 * j)) 16)
          (by rw [length_bytesAt, length_bytesAt]; omega)
      have hz : t'.zf = some (decide (j + 1 = q)) := by
        rw [zf', show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat, sub_beq (by omega) (by omega)]
        congr 1; simp only [decide_eq_decide]; omega
      have gg : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → t'.gpr r = s.gpr r := fun r a b c => by
        rw [g' r c, g r a b c]
      have r10'' : t'.gpr .r10 = BitVec.ofNat 64 (16 * (j + 1)) := by
        rw [r10', show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]; congr 1
      by_cases he : j + 1 = q
      · left
        refine ⟨by simp [eval, hz, he], by rw [r10'', he], by rw [hmem, he], gg, by rw [rd', rd],
          by rw [wr', wr], z.trans z'⟩
      · right
        refine ⟨by simp [eval, hz, he], q - (j + 1), by omega, j + 1, rfl, by omega, r10'', hmem, gg,
          by rw [g' _ (by decide), r8], by rw [rd', rd], by rw [wr', wr], z.trans z'⟩
  refine WP.seq (WP.mono mid fun s₂ ⟨r10₂, m₂, g₂, rd₂, wr₂, z₂⟩ => ?_)
  -- The last `n mod 16` bytes, one at a time.
  have hcx : s₂.gpr .rcx = BitVec.ofNat 64 n := by rw [g₂ _ (by decide) (by decide) (by decide), h.rcx]
  refine WP.seq (WP.mono (Q := fun (t : State) => t.zf = some (decide (16 * q = n)) ∧ t.gpr = s₂.gpr ∧ t.mem = s₂.mem ∧
      t.rd = s₂.rd ∧ t.wr = s₂.wr ∧ ZKeep [] s₂ t) ?_ fun s₃ ⟨zf₃, g₃, m₃, rd₃, wr₃, z₃⟩ => ?_)
  · apply WP.of_runBlock
    refine ⟨_, by xrun [r10₂, hcx], ?_⟩
    refine ⟨?_, by simp [gpr_arithFlags], rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
    simp only [zf_arithFlags]; rw [sub_beq (by omega) (by omega)]
  refine WP.ite (decide (16 * q = n)) (by simp only [eval, zf₃]) (fun hz => ?_) (fun hz => ?_)
  · have hq : 16 * q = n := of_decide_eq_true hz
    exact WP.block_nil ⟨by rw [m₃, m₂, hq], fun r a b c => by rw [g₃, g₂ r a b c], by rw [rd₃, rd₂],
      by rw [wr₃, wr₂], z₂.trans (z₃.mono (by simp))⟩
  · have hq : 16 * q < n := by have := of_decide_eq_false hz; omega
    refine WP.loop (M := isa) (body := .block copyBody) (c := .ne)
      (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
        t.mem = writeBytes s.mem D (bytesAt s.mem S i) ∧
        (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        ZKeep [.xmm4] s t) ?_ (n - 16 * q) _
      ⟨16 * q, rfl, hq, by rw [g₃, r10₂], by rw [m₃, m₂], fun r a b c => by rw [g₃, g₂ r a b c],
        by rw [rd₃, rd₂], by rw [wr₃, wr₂], z₂.trans (z₃.mono (by simp))⟩
    rintro k t ⟨i, rfl, hi, r10, mem, g, rd, wr, z⟩
    obtain ⟨t', run', mem', r10', zf', g', rd', wr', z'⟩ := copyStepZ_ok t
      (by rw [g _ (by decide) (by decide) (by decide), h.rsi])
      (by rw [g _ (by decide) (by decide) (by decide), h.rdi]) r10
      (by rw [g _ (by decide) (by decide) (by decide), h.rcx])
      (by rw [rd, wr]; exact in_of_covers h.rd hi (by omega))
      (by rw [wr]; exact in_of_covers h.wr hi (by omega))
    refine WP.of_runBlock ⟨t', run', ?_⟩
    have hlen : (bytesAt s.mem S i).length = i := length_bytesAt _ _ _
    have hmem : t'.mem = writeBytes s.mem D (bytesAt s.mem S (i + 1)) := by
      rw [mem', mem, src_kept h.disj hi h.lt _ hlen, bytesAt_succ,
        writeBytes_snoc s.mem D (bytesAt s.mem S i) _ (by rw [hlen]; omega), hlen]
    have hz : t'.zf = some (decide (i + 1 = n)) := by
      rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    have gg : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → t'.gpr r = s.gpr r := fun r a b c => by
      rw [g' r a c, g r a b c]
    have zk : ZKeep [.xmm4] s t' := z.trans (z'.mono (by simp))
    by_cases he : i + 1 = n
    · left
      exact ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr], zk⟩
    · right
      exact ⟨by simp [eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega, by rw [r10', succ_ofNat],
        hmem, gg, by rw [rd', rd], by rw [wr', wr], zk⟩

end VG.Proof.AesGcm.X86_64.Short
