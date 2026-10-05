import VerifiedGarbage.Impl.Pbkdf2.Md.Arm
import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Proof.Pbkdf2.MdKeys
import VerifiedGarbage.Proof.Pbkdf2.MdKeys
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Sha256
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Sha512.Scratch
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Finalize
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Sha1.Arm.Stream.Md
import VerifiedGarbage.Proof.Md5.Arm.Stream.Md
import VerifiedGarbage.Proof.Sha1.Arm.Compress
import VerifiedGarbage.Proof.Sha512.Arm.Compress
import VerifiedGarbage.Proof.Sha512.Arm.Shared
import VerifiedGarbage.Proof.Framework.TaintBatch

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Words`. -/
section

/-!
# HMAC and PBKDF2-HMAC over a Merkle–Damgård hash function on ARMv7: words

What the straight-line pieces of `Impl/Pbkdf2/Md/Arm.lean` write, in one run:
copies of 32-bit words (`copyW`), the padding (`padFrom`, then the constant
words `constW` of the length field), `T ← T ⊕ U` (`xorW`), and `scratch` plus
an offset in a register (`scrAt`); and what the code writing a hash function's
digest must do (`OutOk`).
-/

namespace VG.Proof.Pbkdf2.Md.Arm

open VG VG.Arm
open VG.Impl.Pbkdf2.Md.Arm (cp copyW padFrom constW xorW)
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)
open VG.Proof.MdStream (Md bytes32)
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov wp_add wp_ldr wp_str op2_imm op2_reg writeW_le)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append)
open VG.Proof.Hmac.Common (copy_mem bytesAt_zero bytesAt_add bytesAt_length bytesAt_writeBytes_sep
  extractLsb'_read bytesAt_getD')
open VG.Proof.Pbkdf2.Memory (writeW_bytes writeBytes_append' xorBytes_length sep_after off_contains)
open VG.Spec.Sha256 (bytesAt)

/-! ## Single instructions -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_movw {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm.setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movw d imm :: is)) s Q :=
  MdStream.Arm.WP.cons (s' := s.setReg d (imm.setWidth 32)) rfl (k _ (Upd.setReg _ _ _))

theorem wp_movt {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  MdStream.Arm.WP.cons (s' := s.setReg d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32)) rfl
    (k _ (Upd.setReg _ _ _))

theorem wp_eor {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .eor d n o :: is)) s Q :=
  MdStream.Arm.WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

end

theorem add_off (p : Addr) (o j : Nat) :
    p + BitVec.ofNat 64 (o + j) = p + BitVec.ofNat 64 o + BitVec.ofNat 64 j := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem movw_ofNat {n : Nat} (h : n < 2 ^ 16) : (BitVec.ofNat 16 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `d ← scratch + o`, with `scratch` in `r11`. -/
theorem scrAt_ok {d : Reg} {o : Nat} (ho : o < 2 ^ 16) {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ d → r ≠ .r12 → s'.gpr r = s.gpr r) → s'.gpr d = s.gpr .r11 + BitVec.ofNat 32 o →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → WP isa (.block rest) s' Q) :
    WP isa (.block (scrAt d o ++ rest)) s Q := by
  simp only [scrAt, List.cons_append, List.nil_append]
  refine VG.Proof.Pbkdf2.Md.Arm.wp_movw fun s₁ u₁ => wp_add (op2_reg _ _) fun s₂ u₂ => k s₂ (fun r h₁ h₂ => ?_) ?_
    (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) (by rw [u₂.sp, u₁.sp])
  · rw [u₂.other r h₁, u₁.other r h₂]
  · rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), VG.Proof.Pbkdf2.Md.Arm.movw_ofNat ho]

/-! ## Copies -/

/-- Copying `n` words from `[src + o₁]` to `[dst + o₂]`, through `r12`. -/
theorem copyW_ok {src dst : Reg} (hs : src ≠ .r12) (hd : dst ≠ .r12) (o₁ o₂ : Nat) (n : Nat)
    (hb : o₁ + 4 * n ≤ 4096 ∧ o₂ + 4 * n ≤ 4096) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (s.gpr src).toNat + o₁ + 4 * n ≤ 2 ^ 32 → (s.gpr dst).toNat + o₂ + 4 * n ≤ 2 ^ 32 →
    (∀ k < n, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr src) + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (State.addr (s.gpr dst) + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * k)) 4) →
    Mem.Sep (State.addr (s.gpr src) + BitVec.ofNat 64 o₁) (4 * n)
      (State.addr (s.gpr dst) + BitVec.ofNat 64 o₂) (4 * n) →
    (∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr (s.gpr dst) + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (State.addr (s.gpr src) + BitVec.ofNat 64 o₁) (4 * n)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block (copyW src dst o₁ o₂ n ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl rfl (by rw [Nat.mul_zero, bytesAt_zero, VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro rest s Q fs fd hin hout hsep k
    rw [copyW, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih ⟨by omega_nat, by omega_nat⟩ _ s Q (by omega_nat) (by omega_nat) (fun j hj => hin j (by omega_nat))
      (fun j hj => hout j (by omega_nat)) (fun x hx hy => hsep x (by omega_nat) (by omega_nat))
      fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [cp, List.cons_append, List.nil_append]
    refine wp_ldr (a := State.addr (s.gpr src) + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * n))
      (by omega_nat) (by rw [g₁ _ hs, addr_add (by omega_nat), VG.Proof.Pbkdf2.Md.Arm.add_off])
      (by rw [rd₁, wr₁]; exact hin n (by omega_nat)) fun s₂ u₂ => ?_
    refine wp_str (a := State.addr (s.gpr dst) + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * n))
      (by omega_nat) (by rw [u₂.other _ hd, g₁ _ hd, addr_add (by omega_nat), VG.Proof.Pbkdf2.Md.Arm.add_off])
      (by rw [u₂.wr, wr₁]; exact hout n (by omega_nat))
      fun s₃ u₃ => k s₃ (fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr])
        (by rw [u₃.rd, u₂.rd, rd₁]) (by rw [u₃.wr, u₂.wr, wr₁]) (by rw [u₃.sp, u₂.sp, sp₁]) ?_
    rw [u₃.mem, u₂.gpr, u₂.mem, m₁, Nat.mul_succ]
    exact copy_mem s.mem _ _ n 4 (by rwa [← Nat.mul_succ]) (by omega_nat)

/-! ## The padding -/

/-- Stores of zero (`r12`) at `r6 + a + 4 + 4 k`, for `k < n`. -/
theorem zeros_ok {a : Nat} {p : BitVec 32} : ∀ n, a + 4 + 4 * n ≤ 4096 → p.toNat + a + 4 + 4 * n ≤ 2 ^ 32 →
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr .r6 = p → s.gpr .r12 = 0 →
    (∀ k < n, InRegions s.wr (State.addr p + BitVec.ofNat 64 (a + 4 + 4 * k)) 4) →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr p + BitVec.ofNat 64 (a + 4)) (List.replicate (4 * n) 0) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).map (fun k => Instr.str .r12 .r6 (a + 4 + 4 * k)) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ _ rest s Q _ _ _ k
    exact k s rfl rfl rfl rfl (by simp [VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro ha hf rest s Q h6 h12 hout k
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    refine ih (by omega_nat) (by omega_nat) _ s Q h6 h12 (fun j hj => hout j (by omega_nat))
      fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_str (a := State.addr p + BitVec.ofNat 64 (a + 4 + 4 * n)) (by omega_nat)
      (by rw [g₁, h6, addr_add (by omega_nat)]) (by rw [wr₁]; exact hout n (by omega_nat)) fun s₂ g₂ =>
        k s₂ (by rw [g₂.gpr, g₁]) (by rw [g₂.rd, rd₁]) (by rw [g₂.wr, wr₁]) (by rw [g₂.sp, sp₁]) ?_
    rw [g₂.mem, g₁, h12, m₁, writeW_bytes _ _ (0 : BitVec 32) [0, 0, 0, 0] (by decide),
      writeBytes_append' _ _ _ (by rw [List.length_replicate, Memory.add_ofNat])
        (by simp; omega_nat), Nat.mul_succ, ← List.replicate_append_replicate]
    rfl

/-- `padFrom a b` writes `0x80` and zeros from byte `a` to byte `b` of the block at `r6`. -/
theorem padFrom_ok {a b : Nat} (hab : a + 4 ≤ b) (h4 : (b - a) % 4 = 0) (hb : b ≤ 4096) {s : State} {p : BitVec 32}
    (h6 : s.gpr .r6 = p) (hf : p.toNat + b ≤ 2 ^ 32)
    (hout : ∀ k < (b - a) / 4, InRegions s.wr (State.addr p + BitVec.ofNat 64 (a + 4 * k)) 4)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr p + BitVec.ofNat 64 a) ([0x80] ++ List.replicate (b - a - 1) 0) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (padFrom a b ++ rest)) s Q := by
  unfold padFrom
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  refine wp_str (a := State.addr p + BitVec.ofNat 64 a) (by omega_nat)
    (by rw [u₁.other _ (by decide), h6, addr_add (by omega_nat)])
    (by rw [u₁.wr]; simpa using hout 0 (by omega_nat)) fun s₂ g₂ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine VG.Proof.Pbkdf2.Md.Arm.zeros_ok (a := a) (p := p) ((b - a) / 4 - 1) (by omega_nat) (by omega_nat) rest s₃ Q
    (by rw [u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h6]) u₃.gpr
    (fun j hj => by
      rw [u₃.wr, g₂.wr, u₁.wr, show a + 4 + 4 * j = a + 4 * (j + 1) by omega_nat]; exact hout (j + 1) (by omega_nat))
    fun s₄ g₄ rd₄ wr₄ sp₄ m₄ => k s₄ (fun r hr => by
      rw [g₄, u₃.other r hr, g₂.gpr, u₁.other r hr]) (by rw [rd₄, u₃.rd, g₂.rd, u₁.rd])
      (by rw [wr₄, u₃.wr, g₂.wr, u₁.wr]) (by rw [sp₄, u₃.sp, g₂.sp, u₁.sp]) ?_
  rw [m₄, u₃.mem, g₂.mem, u₁.gpr, u₁.mem,
    writeW_bytes _ _ (0x80 : BitVec 32) [0x80, 0, 0, 0] (by decide),
    writeBytes_append' _ _ _ (by rw [List.length_cons, List.length_cons, List.length_cons,
      List.length_singleton, Memory.add_ofNat]) (by simp; omega_nat),
    show b - a - 1 = 3 + 4 * ((b - a) / 4 - 1) by omega_nat, ← List.replicate_append_replicate]
  rfl

/-- The bytes of words, each stored little-endian. -/
def wordsBytes (ws : List (BitVec 32)) : List Byte := ws.flatMap (bytes32 false)

theorem wordsBytes_length (ws : List (BitVec 32)) : (VG.Proof.Pbkdf2.Md.Arm.wordsBytes ws).length = 4 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [VG.Proof.Pbkdf2.Md.Arm.wordsBytes, List.flatMap_cons, List.length_append, MdStream.bytes32_length] at ih ⊢
    rw [ih, List.length_cons]; omega

theorem movw_movt' (x : BitVec 32) :
    (x.extractLsb' 16 16 ++ ((x.extractLsb' 0 16).setWidth 32).extractLsb' 0 16 : BitVec 32) = x :=
  movw_movt x

/-- `constW o ws` stores the words `ws` from `r6 + o` on. -/
theorem constW_ok {p : BitVec 32} : ∀ (ws : List (BitVec 32)) (o : Nat), o + 4 * ws.length ≤ 4096 →
    p.toNat + o + 4 * ws.length ≤ 2 ^ 32 →
    ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .r6 = p →
    (∀ k < ws.length, InRegions s.wr (State.addr p + BitVec.ofNat 64 (o + 4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr p + BitVec.ofNat 64 o) (VG.Proof.Pbkdf2.Md.Arm.wordsBytes ws) →
      WP isa (.block rest) s' Q) →
    WP isa (.block (constW o ws ++ rest)) s Q
  | [], o, _, _, rest, s, Q, _, _, k => k s (fun _ _ => rfl) rfl rfl rfl (by rw [VG.Proof.Pbkdf2.Md.Arm.wordsBytes, List.flatMap_nil,
      VG.WriteBytes.writeBytes_nil])
  | w :: ws, o, ho, hf, rest, s, Q, h6, hout, k => by
    simp only [List.length_cons] at ho hf
    simp only [constW, List.cons_append, List.nil_append]
    refine VG.Proof.Pbkdf2.Md.Arm.wp_movw fun s₁ u₁ => VG.Proof.Pbkdf2.Md.Arm.wp_movt fun s₂ u₂ => ?_
    have e6 : s₂.gpr .r6 = p := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h6]
    refine wp_str (a := State.addr p + BitVec.ofNat 64 o) (by omega_nat) (by rw [e6, addr_add (by omega_nat)])
      (by rw [u₂.wr, u₁.wr]; simpa using hout 0 (by simp)) fun s₃ g₃ => ?_
    refine VG.Proof.Pbkdf2.Md.Arm.constW_ok (p := p) ws (o + 4) (by omega_nat) (by omega_nat) rest s₃ Q (by rw [g₃.gpr, e6])
      (fun j hj => by
        rw [g₃.wr, u₂.wr, u₁.wr, show o + 4 + 4 * j = o + 4 * (j + 1) by omega_nat]
        exact hout (j + 1) (by simp; omega_nat)) fun s₄ g₄ rd₄ wr₄ sp₄ m₄ => ?_
    refine k s₄ (fun r hr => by rw [g₄ r hr, g₃.gpr, u₂.other r hr, u₁.other r hr])
      (by rw [rd₄, g₃.rd, u₂.rd, u₁.rd]) (by rw [wr₄, g₃.wr, u₂.wr, u₁.wr]) (by rw [sp₄, g₃.sp, u₂.sp, u₁.sp]) ?_
    have v : s₂.gpr .r12 = w := by rw [u₂.gpr, u₁.gpr, VG.Proof.Pbkdf2.Md.Arm.movw_movt']
    rw [m₄, g₃.mem, v, u₂.mem, u₁.mem, writeW_le,
      writeBytes_append' _ _ _ (by rw [MdStream.bytes32_length, Memory.add_ofNat]) (by
        rw [MdStream.bytes32_length, VG.Proof.Pbkdf2.Md.Arm.wordsBytes_length]; omega_nat)]
    rfl

/-! ## `T ← T ⊕ U` -/

theorem writeW_xor32 (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 32 ^^^ m'.readW b 32) =
      VG.WriteBytes.writeBytes m d (Spec.Pbkdf2.xorBytes (bytesAt m' b 4) (bytesAt m' a 4)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (32 : Nat) / 8 = 4 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    VG.WriteBytes.write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [Spec.Pbkdf2.xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [Spec.Pbkdf2.xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read _ _ h₁, Mem.extractLsb'_read _ _ h₁, BitVec.xor_comm]

/-- `T ← T ⊕ U` for the first `n` words of `T` at `r7` (`tp`) and `U` at `r6` (`bp`). -/
theorem xor_ok {tp bp : BitVec 32} {D : Nat} (hd : Region.Disjoint ⟨State.addr tp, D⟩ ⟨State.addr bp, D⟩)
    (hD : D ≤ 4096) (ft : tp.toNat + D ≤ 2 ^ 32) (fb : bp.toNat + D ≤ 2 ^ 32) :
    ∀ n, 4 * n ≤ D → ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .r6 = bp → s.gpr .r7 = tp →
    (∀ k < n, InRegions (s.rd ++ s.wr) (State.addr bp + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (State.addr tp + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .r12 → r ≠ .r1 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr tp)
        (Spec.Pbkdf2.xorBytes (bytesAt s.mem (State.addr tp) (4 * n)) (bytesAt s.mem (State.addr bp) (4 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap xorW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ k
    exact k s (fun _ _ _ => rfl) rfl rfl rfl (by simp [bytesAt, Spec.Pbkdf2.xorBytes, VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q h6 h7 hin hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega_nat) _ s Q h6 h7 (fun j hj => hin j (by omega_nat)) (fun j hj => hout j (by omega_nat))
      fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [xorW, List.cons_append, List.nil_append]
    have hw := hout n (by omega_nat)
    refine wp_ldr (a := State.addr bp + BitVec.ofNat 64 (4 * n)) (by omega_nat)
      (by rw [g₁ _ (by decide) (by decide), h6, addr_add (by omega_nat)]) (by rw [rd₁, wr₁]; exact hin n (by omega_nat))
      fun s₂ u₂ => ?_
    refine wp_ldr (a := State.addr tp + BitVec.ofNat 64 (4 * n)) (by omega_nat)
      (by rw [u₂.other _ (by decide), g₁ _ (by decide) (by decide), h7, addr_add (by omega_nat)])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; obtain ⟨r, hr, hc⟩ := hw; exact ⟨r, List.mem_append_right _ hr, hc⟩)
      fun s₃ u₃ => ?_
    refine VG.Proof.Pbkdf2.Md.Arm.wp_eor (op2_reg _ _) fun s₄ u₄ => ?_
    refine wp_str (a := State.addr tp + BitVec.ofNat 64 (4 * n)) (by omega_nat)
      (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        g₁ _ (by decide) (by decide), h7, addr_add (by omega_nat)])
      (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]; exact hw)
      fun s₅ g₅ => k s₅ (fun r h12 h1 => by
          rw [g₅.gpr, u₄.other r h12, u₃.other r h1, u₂.other r h12, g₁ r h12 h1])
        (by rw [g₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [g₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
        (by rw [g₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]) ?_
    have hl : (Spec.Pbkdf2.xorBytes (bytesAt s.mem (State.addr tp) (4 * n))
        (bytesAt s.mem (State.addr bp) (4 * n))).length = 4 * n := by
      rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    have v : s₄.gpr .r12 = s₁.mem.readW (State.addr bp + BitVec.ofNat 64 (4 * n)) 32 ^^^
        s₁.mem.readW (State.addr tp + BitVec.ofNat 64 (4 * n)) 32 := by
      rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₃.gpr, u₂.mem]
    rw [g₅.mem, u₄.mem, u₃.mem, u₂.mem, v, VG.Proof.Pbkdf2.Md.Arm.writeW_xor32, m₁,
      bytesAt_writeBytes_sep (p := State.addr tp + BitVec.ofNat 64 (4 * n)),
      bytesAt_writeBytes_sep (p := State.addr bp + BitVec.ofNat 64 (4 * n))]
    · have e := VG.WriteBytes.writeBytes_append s.mem (State.addr tp) _
        (Spec.Pbkdf2.xorBytes (bytesAt s.mem (State.addr tp + BitVec.ofNat 64 (4 * n)) 4)
          (bytesAt s.mem (State.addr bp + BitVec.ofNat 64 (4 * n)) 4))
        (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega_nat)
      rw [hl] at e
      rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, Spec.Pbkdf2.xorBytes, Spec.Pbkdf2.xorBytes,
        Spec.Pbkdf2.xorBytes, List.zipWith_append (by simp [bytesAt])]
    · intro x h₁ h₂
      rw [hl] at h₂
      exact hd x (by simp only [Region.Contains]; omega_nat) (off_contains h₁ (by omega_nat) (by omega_nat))
    · omega_nat
    · intro x h₁ h₂
      rw [hl] at h₂
      exact sep_after h₁ h₂ (by omega_nat)
    · omega_nat

/-! ## Digests -/

/-- What the code writing a hash function's digest must do: write the digest
of the hash value at `r0` to `r6`, writing only `r9` and `r10`. -/
def OutOk {B N L : Nat} (H : Md B N L) (out : List Instr) : Prop :=
  ∀ s : State, (s.gpr .r0).toNat + N ≤ 2 ^ 32 → (s.gpr .r6).toNat + N ≤ 2 ^ 32 →
    InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0)) N → InRegions s.wr (State.addr (s.gpr .r6)) N →
    Region.Disjoint ⟨State.addr (s.gpr .r0), N⟩ ⟨State.addr (s.gpr .r6), N⟩ →
    WP isa (.block out) s fun s' => (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr (s.gpr .r6)) (H.digest (H.stateAt s.mem (State.addr (s.gpr .r0))))

/-- The streaming proofs' digest code. -/
theorem OutOk.ofShape {P : Impl.MdStream.Arm.Params} {H : Md P.B P.N P.L} (h : MdStream.Arm.Shape H) :
    VG.Proof.Pbkdf2.Md.Arm.OutOk H P.out := fun s f₀ f₆ hin hout hd =>
  h.out s f₀ f₆ hin hout hd

/-! ## Blocks -/

/-- The block, of `D` bytes of message and the padding after them. -/
theorem blockAt_eq {B N L D : Nat} {md : Md B N L} {m : Mem} {p : Addr} (hD : D ≤ B)
    (h : bytesAt m (p + BitVec.ofNat 64 D) (B - D) = md.tailPad D) :
    md.blockAt m p = md.tailBlock D (bytesAt m p D) := by
  simp only [Md.blockAt, Md.tailBlock]
  refine md.parse_congr fun k hk => ?_
  have e := bytesAt_add m p D (B - D)
  rw [h, show D + (B - D) = B by omega] at e
  rw [← e, bytesAt_getD' _ _ hk]

end VG.Proof.Pbkdf2.Md.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Compress`. -/
section

/-!
# A Merkle–Damgård compression function on ARMv7, called on one block

As on AArch64 (`Proof/Pbkdf2/AArch64/Compress.lean`): the contract of a
compression function with blocks of any size `B` (`compK`, which is that of
the streaming proofs, `Proof/MdStream/Arm/Common.lean`, for any block size,
and each hash function's own, `Proof.Sha1.compressArm` and the others, at its
sizes), what its callers need of an implementation (`CompOk`: correct,
constant time, without calls, never writing `r0` or `r3`), and the call of it
on the block at `r6` (`compressBlock`), in one run (`compressBlock_ok`) and in
two (`compressBlock_rel`).
-/

namespace VG.Proof.Pbkdf2.Md.Arm

open VG VG.Arm VG.Proof.MdStream
open VG.Impl.MdStream.Arm (compressAt compressWith)
open VG.Proof.MdStream.Arm (Upd wp_mov op2_imm op2_reg)

section
variable {B N L : Nat} (H : Md B N L) (so : Nat)

/-- The contract of the compression function: updates the `N`-byte hash
value at `r0` with the `r2` blocks of `B` bytes at `r1`, with scratch space
`r3` (`so` bytes). -/
def compK : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), N⟩
    let blocks : Region := ⟨State.addr (s.gpr .r1), B * (s.gpr .r2).toNat⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), so⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    (s.gpr .r0).toNat + N ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + B * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + so ≤ 2 ^ 32
  post s s' :=
    H.stateAt s'.mem (State.addr (s.gpr .r0)) =
      H.compressBlocks (H.stateAt s.mem (State.addr (s.gpr .r0))) s.mem (State.addr (s.gpr .r1))
        (s.gpr .r2).toNat
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

/-- What a caller needs of an implementation of the compression function:
that it is correct and constant time, makes no calls, and never writes `r0`
or `r3`. -/
structure CompOk (code : Prog isa) : Prop where
  verified : ∀ s, (VG.Proof.Pbkdf2.Md.Arm.compK H so).pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (VG.Proof.Pbkdf2.Md.Arm.compK H so).post s s'
  ct : ConstantTime isa (VG.Proof.Pbkdf2.Md.Arm.compK H so).pre (VG.Proof.Pbkdf2.Md.Arm.compK H so).pub code
  noCalls : code.noCalls = true
  keeps : ((instrs code).all fun i => dstOf i != some .r0 && dstOf i != some .r3) = true

end

/-- The call of the compression function on the block at `r6`. -/
abbrev compressBlock (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [.mov .r1 (.reg .r6)]) (VG.Impl.MdStream.Arm.compressAt name code)

section
variable {B N L : Nat} {H : Md B N L} {so : Nat}

/-- What the call of the compression function on the block at `r6` (`src`),
into the hash value at `r0` (`st`), with scratch space at `r3` (`scr`),
needs. -/
structure CallOk (s : State) (N B so : Nat) (st scr src : BitVec 32) : Prop where
  r0 : s.gpr .r0 = st
  r3 : s.gpr .r3 = scr
  r6 : s.gpr .r6 = src
  f₀ : st.toNat + N ≤ 2 ^ 32
  f₁ : src.toNat + B ≤ 2 ^ 32
  f₃ : scr.toNat + so ≤ 2 ^ 32
  st_scr : Region.Disjoint ⟨State.addr st, N⟩ ⟨State.addr scr, so⟩
  src_st : Region.Disjoint ⟨State.addr src, B⟩ ⟨State.addr st, N⟩
  src_scr : Region.Disjoint ⟨State.addr src, B⟩ ⟨State.addr scr, so⟩
  cov : Covers [⟨State.addr src, B⟩, ⟨State.addr st, N⟩, ⟨State.addr scr, so⟩] (s.rd ++ s.wr)
  covW : Covers [⟨State.addr st, N⟩, ⟨State.addr scr, so⟩] s.wr

/-- The state after the instructions that set up the call. -/
structure CSetup (s t : State) : Prop where
  r1 : t.gpr .r1 = s.gpr .r6
  r2 : t.gpr .r2 = 1
  other : ∀ r, r ≠ .r1 → r ≠ .r2 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem csetup_ok {name : String} {code : Prog isa} (s : State) {Q : State → Prop} (k : ∀ t, VG.Proof.Pbkdf2.Md.Arm.CSetup s t → WP isa (.call name code) t Q) :
    WP isa (VG.Proof.Pbkdf2.Md.Arm.compressBlock name code) s Q := by
  unfold VG.Proof.Pbkdf2.Md.Arm.compressBlock VG.Impl.MdStream.Arm.compressAt compressWith
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁ u₁ => WP.block_nil ?_)
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₂ u₂ => WP.block_nil (k s₂ ?_))
  exact ⟨by rw [u₂.other _ (by decide), u₁.gpr], u₂.gpr, fun r h1 h2 => by rw [u₂.other r h2, u₁.other r h1],
    by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp]⟩

theorem one32 : (1 : BitVec 32).toNat = 1 := rfl

theorem call_pre {s t : State} {st scr src : BitVec 32} (h : VG.Proof.Pbkdf2.Md.Arm.CallOk s N B so st scr src) (hs : VG.Proof.Pbkdf2.Md.Arm.CSetup s t) :
    (VG.Proof.Pbkdf2.Md.Arm.compK H so).pre (t.callEntry.withRegions [⟨State.addr src, B⟩] [⟨State.addr st, N⟩, ⟨State.addr scr, so⟩]) := by
  have c0 : t.callEntry.gpr .r0 = st :=
    (State.callEntry_gpr _ (by decide)).trans ((hs.other _ (by decide) (by decide)).trans h.r0)
  have c1 : t.callEntry.gpr .r1 = src := (State.callEntry_gpr _ (by decide)).trans (hs.r1.trans h.r6)
  have c2 : t.callEntry.gpr .r2 = 1 := (State.callEntry_gpr _ (by decide)).trans hs.r2
  have c3 : t.callEntry.gpr .r3 = scr :=
    (State.callEntry_gpr _ (by decide)).trans ((hs.other _ (by decide) (by decide)).trans h.r3)
  simp only [VG.Proof.Pbkdf2.Md.Arm.compK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, c0, c1, c2, c3, VG.Proof.Pbkdf2.Md.Arm.one32,
    Nat.mul_one]
  exact ⟨trivial, trivial, h.st_scr, h.src_st, h.src_scr, h.f₀, h.f₁, h.f₃⟩

/-- Compressing the block at `r6` into the hash value at `r0`, with scratch
space at `r3`: the callee-saved registers other than `lr`, and `r0` and `r3`,
are kept. -/
theorem compressBlock_ok {name : String} {code : Prog isa} (hf : VG.Proof.Pbkdf2.Md.Arm.CompOk H so code) {s : State}
    {st scr src : BitVec 32} (h : VG.Proof.Pbkdf2.Md.Arm.CallOk s N B so st scr src) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      s'.gpr .r0 = st → s'.gpr .r3 = scr → s'.sp = s.sp →
      Frame [⟨State.addr st, N⟩, ⟨State.addr scr, so⟩] s.mem s'.mem →
      H.stateAt s'.mem (State.addr st) =
        H.compress (H.stateAt s.mem (State.addr st)) (H.blockAt s.mem (State.addr src)) → Q s') :
    WP isa (VG.Proof.Pbkdf2.Md.Arm.compressBlock name code) s Q := by
  have hk : ∀ i ∈ instrs code, dstOf i ≠ some .r0 ∧ dstOf i ≠ some .r3 := by
    intro i hi
    have := List.all_eq_true.mp hf.keeps i hi
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    exact this
  refine VG.Proof.Pbkdf2.Md.Arm.csetup_ok s fun t hs => ?_
  refine WP.call (k := VG.Proof.Pbkdf2.Md.Arm.compK H so) hf.verified (VG.Proof.Pbkdf2.Md.Arm.call_pre h hs) ?_ ?_ ?_ hf.noCalls
  · rw [hs.rd, hs.wr]; simpa using h.cov
  · rw [hs.wr]; exact h.covW
  · intro s' hrd hwr hsp hfr hcs hg hpost
    have c0 : t.callEntry.gpr .r0 = st :=
      (State.callEntry_gpr _ (by decide)).trans ((hs.other _ (by decide) (by decide)).trans h.r0)
    have c1 : t.callEntry.gpr .r1 = src := (State.callEntry_gpr _ (by decide)).trans (hs.r1.trans h.r6)
    have c2 : (t.callEntry.gpr .r2).toNat = 1 := by rw [State.callEntry_gpr _ (by decide), hs.r2]; rfl
    simp only [VG.Proof.Pbkdf2.Md.Arm.compK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2,
      hs.mem] at hpost
    rw [hs.mem] at hfr
    refine hQ s' (hrd.trans hs.rd) (hwr.trans hs.wr) (fun r hr hlr => ?_)
      (by rw [hg _ (fun i hi => (hk i hi).1) (by decide), hs.other _ (by decide) (by decide), h.r0])
      (by rw [hg _ (fun i hi => (hk i hi).2) (by decide), hs.other _ (by decide) (by decide), h.r3])
      (hsp.trans hs.sp) hfr ?_
    · have : r ≠ .r1 ∧ r ≠ .r2 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hcs r hr hlr, hs.other r this.1 this.2]
    · rw [hpost, Md.compressBlocks_one]

/-- `compressBlock` is constant time, in runs that call it on the same regions. -/
theorem compressBlock_rel {name : String} {code : Prog isa} (hf : VG.Proof.Pbkdf2.Md.Arm.CompOk H so code) {st scr src : BitVec 32}
    {P' : State → State → Prop}
    (hP : ∀ s₁ s₂, P' s₁ s₂ → VG.Proof.Pbkdf2.Md.Arm.CallOk s₁ N B so st scr src ∧ VG.Proof.Pbkdf2.Md.Arm.CallOk s₂ N B so st scr src) :
    RelCT isa P' (VG.Proof.Pbkdf2.Md.Arm.compressBlock name code) fun _ _ => True := by
  unfold VG.Proof.Pbkdf2.Md.Arm.compressBlock VG.Impl.MdStream.Arm.compressAt compressWith
  let M₁ : State → Prop := fun a => ∃ s, VG.Proof.Pbkdf2.Md.Arm.CallOk s N B so st scr src ∧ Upd s a .r1 (s.gpr .r6)
  let M₂ : State → Prop := fun b => ∃ s, VG.Proof.Pbkdf2.Md.Arm.CallOk s N B so st scr src ∧ VG.Proof.Pbkdf2.Md.Arm.CSetup s b
  have w₁ : ∀ s, VG.Proof.Pbkdf2.Md.Arm.CallOk s N B so st scr src → WP isa (.block [.mov .r1 (.reg .r6)]) s M₁ :=
    fun s h => wp_mov (op2_reg _ _) fun a u => WP.block_nil ⟨s, h, u⟩
  have w₂ : ∀ a, M₁ a → WP isa (.block [.mov .r2 (.imm 1)]) a M₂ := fun a ⟨s, h, u₁⟩ =>
    wp_mov (op2_imm (by decide)) fun b u₂ => WP.block_nil ⟨s, h, by rw [u₂.other _ (by decide), u₁.gpr], u₂.gpr,
      fun r h1 h2 => by rw [u₂.other r h2, u₁.other r h1], by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd],
      by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp]⟩
  have su₁ : RelCT isa P' (.block [.mov .r1 (.reg .r6)]) fun a b => M₁ a ∧ M₁ b :=
    ((RelCT.taint (A := taint) (P := P') (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs fun r hr => by
      simp at hr) (by taint_decide)).wp fun s₁ s₂ hp => ⟨w₁ s₁ (hP s₁ s₂ hp).1, w₁ s₂ (hP s₁ s₂ hp).2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have su₂ : RelCT isa (fun a b => M₁ a ∧ M₁ b) (.block [.mov .r2 (.imm 1)]) fun a b => M₂ a ∧ M₂ b :=
    ((RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs fun r hr => by
      simp at hr) (by taint_decide)).wp fun a b h => ⟨w₂ a h.1, w₂ b h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  refine su₁.seq (su₂.seq (RelCT.call (k := VG.Proof.Pbkdf2.Md.Arm.compK H so) hf.verified hf.ct [⟨State.addr src, B⟩]
    [⟨State.addr st, N⟩, ⟨State.addr scr, so⟩] fun t₁ t₂ ⟨⟨σ₁, c₁, h₁⟩, ⟨σ₂, c₂, h₂⟩⟩ => ?_))
  refine ⟨VG.Proof.Pbkdf2.Md.Arm.call_pre c₁ h₁, VG.Proof.Pbkdf2.Md.Arm.call_pre c₂ h₂, ?_, by rw [h₁.rd, h₁.wr]; simpa using c₁.cov, by rw [h₁.wr]; exact c₁.covW,
    by rw [h₂.rd, h₂.wr]; simpa using c₂.cov, by rw [h₂.wr]; exact c₂.covW⟩
  simp only [VG.Proof.Pbkdf2.Md.Arm.compK, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    h₁.r1, h₂.r1, h₁.r2, h₂.r2, h₁.other .r0 (by decide) (by decide), h₂.other .r0 (by decide) (by decide),
    h₁.other .r3 (by decide) (by decide), h₂.other .r3 (by decide) (by decide), c₁.r0, c₂.r0, c₁.r3, c₂.r3,
    c₁.r6, c₂.r6]
  exact ⟨trivial, trivial, trivial, trivial⟩

end

end VG.Proof.Pbkdf2.Md.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Hash`. -/
section

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on ARMv7: the hash function

As on AArch64 (`Proof/Pbkdf2/Md/AArch64/Hash.lean`), `HashOK H` is what the
proofs know of the hash function whose code `H` describes: it is a
Merkle–Damgård hash function `md` (`Md`) whose digest code does what it should
(`OutOk`) and whose length field for a `B + D`-byte message is the constant
words the code stores (`len`), with a verified compression function
(`CompOk`); its streaming functions are verified against the contracts HMAC's
generic proofs call them with (`stream`); its specification is `md` from the
initial hash value `iv` (a state represents a message as the specification
has it exactly when it does as `md` has it: `repr`, `back`), with the digest
the first `D` bytes of `md`'s; and
its sizes fit (`Sizes`).
-/

namespace VG.Proof.Pbkdf2.Md.Arm

open VG.Arm VG.Proof.MdStream
open VG.Impl.Pbkdf2.Md.Arm (Hash lenWords)
open Spec.Hmac (StreamingHash)

/-- The sizes the proofs support, checked for each hash function by
`decide`: words of 4 bytes, a digest of at most the hash value, room for the
padding in the block after the digest and after the hash value, the
streaming state as the hash value followed by a block, `finalize` writing
the whole hash value, and the compression function's scratch space within
the working space of the functions we call. -/
structure Sizes (H : Hash) : Prop where
  B : H.B = 64 ∨ H.B = 128
  N4 : H.N % 4 = 0
  D4 : H.D % 4 = 0
  L4 : H.L % 4 = 0
  D0 : 0 < H.D
  DN : H.D ≤ H.N
  NL : H.N + H.L ≤ H.B
  pad : H.D + 4 ≤ H.B - H.L
  N64 : H.N ≤ 64
  L16 : H.L ≤ 16
  so : H.so ≤ 8 * H.st.W
  W : H.st.W ≤ 64
  S : H.st.S = H.N + H.B
  F : H.st.F = H.N

/-- What the proofs need of a Merkle–Damgård hash function's code. -/
structure HashOK (H : Hash) where
  /-- The hash function, as the proofs see it. -/
  md : Md H.B H.N H.L
  out : VG.Proof.Pbkdf2.Md.Arm.OutOk md H.out
  /-- The compression function is verified. -/
  comp : VG.Proof.Pbkdf2.Md.Arm.CompOk md H.so H.compC
  /-- The hash value is determined by its bytes, wherever they are. -/
  reloc : md.Reloc
  /-- The constant length field is that of a `B + D`-byte message. -/
  len : VG.Proof.Pbkdf2.Md.Arm.wordsBytes (lenWords H.be H.L (H.B + H.D)) = md.lenBytes (H.B + H.D)
  /-- The streaming functions, verified. -/
  stream : Pbkdf2.Stream.Arm.HashOK H.st
  /-- The specification is `md` from `iv`, with a `D`-byte digest. -/
  iv : md.HV
  repr : ∀ mem p m, stream.SH.Repr mem p m → md.Repr iv mem p m
  back : ∀ mem p m, md.Repr iv mem p m → stream.SH.Repr mem p m
  hash : ∀ m, stream.SH.H.hash m = (md.hash iv m).take H.D
  sizes : VG.Proof.Pbkdf2.Md.Arm.Sizes H

namespace HashOK

variable {H : Hash} (hH : VG.Proof.Pbkdf2.Md.Arm.HashOK H)

/-- The specification. -/
abbrev SH : StreamingHash := hH.stream.SH

theorem hB : hH.SH.H.blockSize = H.B := hH.stream.hB
theorem hS : hH.SH.stateBytes = H.N + H.B := hH.stream.hS.trans hH.sizes.S
theorem hD : hH.SH.digestBytes = H.D := hH.stream.hD

include hH in
theorem B_le : H.B ≤ 128 := by rcases hH.sizes.B with h | h <;> omega

include hH in
theorem B_ge : 64 ≤ H.B := by rcases hH.sizes.B with h | h <;> omega

include hH in
theorem B4 : H.B % 4 = 0 := by rcases hH.sizes.B with h | h <;> omega

/-- The hash function of the specification is `md` from `iv`. -/
theorem link : hH.md.Link hH.SH hH.iv H.D :=
  ⟨hH.hB, hH.hS, hH.hD, hH.repr, hH.hash, hH.sizes.DN, by have := hH.sizes.pad; have := hH.sizes.NL; omega⟩

/-- The length field's bytes, as stored. -/
theorem lenBytes_eq : VG.Proof.Pbkdf2.Md.Arm.wordsBytes (lenWords H.be H.L (H.B + H.D)) = hH.md.lenBytes (H.B + H.D) := hH.len

theorem lenWords_length : (lenWords H.be H.L (H.B + H.D)).length = H.L / 4 := by simp [lenWords]

end HashOK

end VG.Proof.Pbkdf2.Md.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.Arm.HmacFin`. -/
section

/-!
# HMAC's `finalize` over a Merkle–Damgård hash function on ARMv7: correct

`finalize` (`Impl/Pbkdf2/Md/Arm.lean`) finalizes the inner state with the hash
function's streaming `finalize`, in a frame that pushes its stack arguments
(`fin_frame`, `Proof/Pbkdf2/Stream/Arm/Hash.lean`), into the block; copies the
outer state's hash value to the hash value being compressed and writes the
padding after the inner digest; compresses the block once
(`compressBlock_ok`); and writes the digest to `out`. `Md.hmac_outer` says
that this is HMAC. The contract is `finG`
(`Proof/Pbkdf2/Stream/Arm/Hash.lean`), the shared one's at 16 bytes of stack.
-/

namespace VG.Proof.Pbkdf2.Md.Arm.Fin

open VG VG.Arm
open VG.Impl.Pbkdf2.Md.Arm (Hash copyW padFrom constW lenWords)
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)
open VG.Proof.Pbkdf2.Md.Arm
open VG.Proof.MdStream (Md)
open VG.Proof.Pbkdf2.Stream.Arm (finG below count SavedRegs saveR savedRegs preserved_saved FinArgs fin_frame
  After below_eq)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_ldrSp op2_reg)
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.Hmac.Common (bytesAt_add bytesAt_length bytesAt_writeBytes_sep writeBytes_at bytesAt_getD')
open VG.Proof.Hmac.Generic.Common (bytesAt_take bytesAt_writeBytes_self' sub_of_off sub_of_self)
open VG.Spec.Hmac (xorPad ipad opad hmacBlockKey)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev inn : BitVec 32 := s₀.gpr .r0
abbrev outer : BitVec 32 := s₀.gpr .r1
abbrev op : BitVec 32 := stackArg s₀ 0
abbrev scr : BitVec 32 := stackArg s₀ 1
abbrev scA : Addr := State.addr (VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀)
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 8⟩

end

section
variable (H : Hash) (sc : Nat) (s₀ : State)

abbrev inR : Region := ⟨State.addr (VG.Proof.Pbkdf2.Md.Arm.Fin.inn s₀), H.N + H.B⟩
abbrev outerR : Region := ⟨State.addr (VG.Proof.Pbkdf2.Md.Arm.Fin.outer s₀), H.N + H.B⟩
abbrev opR : Region := ⟨State.addr (VG.Proof.Pbkdf2.Md.Arm.Fin.op s₀), H.D⟩
abbrev scR : Region := ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.scA s₀, 8 * sc⟩
/-- The hash value being compressed and the block, as registers hold them. -/
abbrev hv : BitVec 32 := VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀ + BitVec.ofNat 32 H.hvO
abbrev blk : BitVec 32 := VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀ + BitVec.ofNat 32 H.blkO
/-- And as addresses. -/
abbrev hvA : Addr := VG.Proof.Pbkdf2.Md.Arm.Fin.scA s₀ + BitVec.ofNat 64 H.hvO
abbrev blkA : Addr := VG.Proof.Pbkdf2.Md.Arm.Fin.scA s₀ + BitVec.ofNat 64 H.blkO

end

structure Pre (H : Hash) (sc : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Pbkdf2.Md.Arm.Fin.outerR H s₀, VG.Proof.Pbkdf2.Md.Arm.Fin.argR s₀]
  wr : s₀.wr = [VG.Proof.Pbkdf2.Md.Arm.Fin.inR H s₀, VG.Proof.Pbkdf2.Md.Arm.Fin.opR H s₀, VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀]
  i_o : (VG.Proof.Pbkdf2.Md.Arm.Fin.inR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.Fin.outerR H s₀)
  i_p : (VG.Proof.Pbkdf2.Md.Arm.Fin.inR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.Fin.opR H s₀)
  i_s : (VG.Proof.Pbkdf2.Md.Arm.Fin.inR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀)
  o_p : (VG.Proof.Pbkdf2.Md.Arm.Fin.outerR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.Fin.opR H s₀)
  o_s : (VG.Proof.Pbkdf2.Md.Arm.Fin.outerR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀)
  p_s : (VG.Proof.Pbkdf2.Md.Arm.Fin.opR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀)
  a_i : (VG.Proof.Pbkdf2.Md.Arm.Fin.argR s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.Fin.inR H s₀)
  a_p : (VG.Proof.Pbkdf2.Md.Arm.Fin.argR s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.Fin.opR H s₀)
  a_s : (VG.Proof.Pbkdf2.Md.Arm.Fin.argR s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀)
  b_i : (below s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.Fin.inR H s₀)
  b_o : (below s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.Fin.outerR H s₀)
  b_p : (below s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.Fin.opR H s₀)
  b_s : (below s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀)
  ni : (VG.Proof.Pbkdf2.Md.Arm.Fin.inn s₀).toNat + (H.N + H.B) ≤ 2 ^ 32
  no : (VG.Proof.Pbkdf2.Md.Arm.Fin.outer s₀).toNat + (H.N + H.B) ≤ 2 ^ 32
  np : (VG.Proof.Pbkdf2.Md.Arm.Fin.op s₀).toNat + H.D ≤ 2 ^ 32
  nw : (VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  sp16 : 16 ≤ s₀.sp.toNat
  spf : s₀.sp.toNat + 8 ≤ 2 ^ 32
  fits : H.st.buf + H.N + H.B ≤ 8 * sc

theorem pre_of {H : Hash} (hH : VG.Proof.Pbkdf2.Md.Arm.HashOK H) {sc : Nat} {s₀ : State} (h : (finG hH.SH sc).pre s₀)
    (hfit : H.st.buf + H.N + H.B ≤ 8 * sc) : VG.Proof.Pbkdf2.Md.Arm.Fin.Pre H sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
  have hS := hH.hS
  have hD := hH.hD
  simp only [hS, hD] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, hfit⟩

theorem buf_eq (H : Hash) : H.st.buf = 8 * H.st.W + 36 := rfl

theorem add0 (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-! ## The parts of the scratch space -/

section
variable {H : Hash} {sc : Nat} (hz : VG.Proof.Pbkdf2.Md.Arm.Sizes H) {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.Arm.Fin.Pre H sc s₀)
include hz hp

omit hz hp in
theorem scr_sub {a n : Nat} (h : a + n ≤ 8 * sc) :
    Region.Sub ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.scA s₀ + BitVec.ofNat 64 a, n⟩ (VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀) :=
  Offset.sub_base _ h

omit hz in
theorem in_scr {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ 8 * sc) :
    InRegions s.wr (VG.Proof.Pbkdf2.Md.Arm.Fin.scA s₀ + BitVec.ofNat 64 a) n :=
  ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀, by simp [hwr, hp.wr], Offset.contains_base _ h (by have hp_nw := hp.nw; omega)⟩

omit hz in
theorem in_scr' {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ 8 * sc) :
    InRegions (s.rd ++ s.wr) (VG.Proof.Pbkdf2.Md.Arm.Fin.scA s₀ + BitVec.ofNat 64 a) n := by
  obtain ⟨r, hr, hc⟩ := VG.Proof.Pbkdf2.Md.Arm.Fin.in_scr hp hwr h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

omit hz in
theorem addr_sO {o : Nat} (h : o < 8 * sc) :
    State.addr (VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀ + BitVec.ofNat 32 o) = VG.Proof.Pbkdf2.Md.Arm.Fin.scA s₀ + BitVec.ofNat 64 o :=
  addr_add (by have hp_nw := hp.nw; omega)

omit hz in
theorem toNat_sO {o : Nat} (h : o < 8 * sc) : (VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀ + BitVec.ofNat 32 o).toNat = (VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀).toNat + o := by
  have hp_nw := hp.nw
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem addr_hv : State.addr (VG.Proof.Pbkdf2.Md.Arm.Fin.hv H s₀) = VG.Proof.Pbkdf2.Md.Arm.Fin.hvA H s₀ := by
  have hp_fits := hp.fits; have hz_N64 := hz.N64; have : 64 ≤ H.B := by rcases hz.B with h | h <;> omega
  exact VG.Proof.Pbkdf2.Md.Arm.Fin.addr_sO hp (by simp only [Hash.hvO]; omega)

theorem addr_blk : State.addr (VG.Proof.Pbkdf2.Md.Arm.Fin.blk H s₀) = VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀ := by
  have hp_fits := hp.fits; have hz_N64 := hz.N64; have : 64 ≤ H.B := by rcases hz.B with h | h <;> omega
  exact VG.Proof.Pbkdf2.Md.Arm.Fin.addr_sO hp (by simp only [Hash.blkO]; omega)

omit hz in
theorem in_blk {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ H.B) :
    InRegions s.wr (VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀ + BitVec.ofNat 64 a) n := by
  have hp_fits := hp.fits
  rw [Memory.add_ofNat]; exact VG.Proof.Pbkdf2.Md.Arm.Fin.in_scr hp hwr (by simp only [Hash.blkO]; omega)

omit hz in
theorem save_sub : Region.Sub (saveR H.st (VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀)) (VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀) := by
  have hp_fits := hp.fits; rw [VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H] at hp_fits; exact VG.Proof.Pbkdf2.Md.Arm.Fin.scr_sub (by omega)

omit hz in
theorem blk_sub : Region.Sub ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀, H.B⟩ (VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀) := by
  have hp_fits := hp.fits; exact VG.Proof.Pbkdf2.Md.Arm.Fin.scr_sub (by simp only [Hash.blkO]; omega)

theorem hv_sub : Region.Sub ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.hvA H s₀, H.N⟩ (VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀) := by
  have hp_fits := hp.fits; have : 64 ≤ H.B := by rcases hz.B with h | h <;> omega
  exact VG.Proof.Pbkdf2.Md.Arm.Fin.scr_sub (by simp only [Hash.hvO]; omega)

/-- The saved registers are outside the hash value, the block and the
working space of the functions we call. -/
theorem save_disj : ∀ r ∈ [⟨VG.Proof.Pbkdf2.Md.Arm.Fin.scA s₀, 8 * H.st.W⟩, ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.hvA H s₀, H.N + H.B⟩, VG.Proof.Pbkdf2.Md.Arm.Fin.inR H s₀, VG.Proof.Pbkdf2.Md.Arm.Fin.opR H s₀, below s₀],
    (saveR H.st (VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀)).Disjoint r := by
  have hz_W := hz.W; have hp_fits := hp.fits; have hp_nw := hp.nw; rw [VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H] at *
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Offset.disjoint _ (.inl (by simp only [Hash.hvO, VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H]; omega)) (by omega)
      (by simp only [Hash.hvO, VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H]; omega)
  · exact (hp.i_s.sub_right (VG.Proof.Pbkdf2.Md.Arm.Fin.save_sub hp)).symm
  · exact (hp.p_s.sub_right (VG.Proof.Pbkdf2.Md.Arm.Fin.save_sub hp)).symm
  · exact (hp.b_s.sub_right (VG.Proof.Pbkdf2.Md.Arm.Fin.save_sub hp)).symm

end

/-! ## What the calls keep -/

/-- The registers and memory kept from the prologue on: memory differs from
the entry's only in the regions we may write and below the stack pointer. -/
structure KR (H : Hash) (sc : Nat) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r5 : s.gpr .r5 = VG.Proof.Pbkdf2.Md.Arm.Fin.outer s₀
  r7 : s.gpr .r7 = VG.Proof.Pbkdf2.Md.Arm.Fin.op s₀
  r11 : s.gpr .r11 = VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀
  saved : SavedRegs H.st (VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀) s₀ s.mem
  frame : Frame [VG.Proof.Pbkdf2.Md.Arm.Fin.inR H s₀, VG.Proof.Pbkdf2.Md.Arm.Fin.opR H s₀, VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀, below s₀] s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.r5, .r7, .r11]

theorem kregs_pres : ∀ r ∈ VG.Proof.Pbkdf2.Md.Arm.Fin.kregs, r ∈ preserved ∧ r ≠ .lr := by decide

section
variable {H : Hash} {sc : Nat} {s₀ : State}

theorem KR.keep {s s' : State} (h : VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ VG.Proof.Pbkdf2.Md.Arm.Fin.kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H.st (VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀)).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [VG.Proof.Pbkdf2.Md.Arm.Fin.inR H s₀, VG.Proof.Pbkdf2.Md.Arm.Fin.opR H s₀, VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀, below s₀], Region.Sub r r') : VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.r5,
    (hg _ (by simp)).trans h.r7, (hg _ (by simp)).trans h.r11, h.saved.frame H.st hf hs,
    h.frame.trans (hf.sub hsub)⟩

theorem KR.upd {s s' : State} (h : VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc s₀ s) {d : Reg} (hd : d ∉ VG.Proof.Pbkdf2.Md.Arm.Fin.kregs) {v : BitVec 32}
    (u : Upd s s' d v) : VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc s₀ s' :=
  h.keep u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp) (by simp)

end

/-! ## The prologue and the call of `finalize` -/

section
variable {H : Hash} (hH : VG.Proof.Pbkdf2.Md.Arm.HashOK H) {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.Arm.Fin.Pre H sc s₀)
include hp

theorem sa1 : stackArgAddr s₀ 1 = stackArgAddr s₀ 0 + BitVec.ofNat 64 4 := by
  have hp_spf := hp.spf
  simp only [stackArgAddr]
  rw [addr_add (k := 4 * 1) (by omega), addr_add (k := 4 * 0) (by omega), BitVec.add_zero]

theorem wr_mem : VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀ ∈ s₀.wr ∧ VG.Proof.Pbkdf2.Md.Arm.Fin.inR H s₀ ∈ s₀.wr ∧ VG.Proof.Pbkdf2.Md.Arm.Fin.opR H s₀ ∈ s₀.wr := by
  rw [hp.wr]; simp

include hH in
theorem pro_ok : WP isa (.block H.finPrologue) s₀ fun s => VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc s₀ s ∧ s.gpr .r0 = VG.Proof.Pbkdf2.Md.Arm.Fin.inn s₀ ∧
    count s = count s₀ ∧ Frame [saveR H.st (VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀)] s₀.mem s.mem := by
  have hz := hH.sizes
  have hW := hz.W; have hf := hp.fits; have nw := hp.nw; rw [VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H] at hf
  obtain ⟨sR, _, _⟩ := VG.Proof.Pbkdf2.Md.Arm.Fin.wr_mem hp
  have aR : VG.Proof.Pbkdf2.Md.Arm.Fin.argR s₀ ∈ s₀.rd ++ s₀.wr := by rw [hp.rd]; simp
  unfold Hash.finPrologue
  simp only [List.singleton_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl
    ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.argR s₀, aR, by rw [VG.Proof.Pbkdf2.Md.Arm.Fin.sa1 hp]; exact Offset.contains_base _ (by omega) (by omega)⟩ fun s₁ u₁ => ?_
  refine Pbkdf2.Stream.Arm.save_ok H.st (scr := VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀) u₁.gpr hW (by rw [u₁.wr]; exact sR) (L := 8 * sc)
    (by omega_using [hf]) nw fun s₂ g₂ rd₂ wr₂ sp₂ f₂ sv₂ => ?_
  have hsp₂ : s₂.sp = s₀.sp := by rw [sp₂, u₁.sp]
  refine wp_mov (op2_reg _ _) fun s₃ u₃ =>
    wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [u₃.sp, hsp₂]; rfl)
      (by rw [u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]
          exact ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.argR s₀, aR, by simp [Region.Contains]⟩) fun s₄ u₄ =>
    wp_mov (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
  have e₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  have hm : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have f₂' : Frame [saveR H.st (VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀)] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  have ea : s₂.mem.readW (stackArgAddr s₀ 0) 32 = VG.Proof.Pbkdf2.Md.Arm.Fin.op s₀ :=
    f₂'.readW (r := ⟨stackArgAddr s₀ 0, 4⟩) (Region.contains_self _ _) (by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hp.a_s.sub_left (Region.sub_prefix (by omega))).sub_right (VG.Proof.Pbkdf2.Md.Arm.Fin.save_sub hp)) (by decide)
  have k : ∀ r, r ≠ .r5 → r ≠ .r7 → r ≠ .r11 → r ≠ .r12 → s₅.gpr r = s₀.gpr r :=
    fun r h5 h7 h11 h12 => by rw [u₅.other r h11, u₄.other r h7, u₃.other r h5, e₂ r h12]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd], by rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₅.sp, u₄.sp, u₃.sp, hsp₂],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, e₂ _ (by decide)],
    by rw [u₅.other _ (by decide), u₄.gpr, u₃.mem, ea],
    by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.gpr]; rfl,
    hm ▸ sv₂.of_eq H.st fun r hr => u₁.other r (by
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    hm ▸ f₂'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀, by simp, VG.Proof.Pbkdf2.Md.Arm.Fin.save_sub hp⟩⟩,
    k _ (by decide) (by decide) (by decide) (by decide),
    by simp only [count, k _ (by decide) (by decide) (by decide) (by decide : Reg.r2 ≠ .r12),
      k _ (by decide) (by decide) (by decide) (by decide : Reg.r3 ≠ .r12)], hm ▸ f₂'⟩

/-- The regions of the call of `finalize` on `inner`, into the block. -/
theorem finArgs {t : State} (hk : VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc s₀ t) (h0 : t.gpr .r0 = VG.Proof.Pbkdf2.Md.Arm.Fin.inn s₀)
    (h1 : t.gpr .r1 = VG.Proof.Pbkdf2.Md.Arm.Fin.blk H s₀) (h12 : t.gpr .r12 = VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀) :
    FinArgs hH.stream t (VG.Proof.Pbkdf2.Md.Arm.Fin.inn s₀) (VG.Proof.Pbkdf2.Md.Arm.Fin.blk H s₀) (VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀) := by
  have hz := hH.sizes
  have hwb := hH.stream.hWb; have hf := hp.fits; have nw := hp.nw; have hz_W := hz.W; have hz_N64 := hz.N64
  have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  have eS := hz.S; have eF := hz.F
  rw [VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H] at hf
  obtain ⟨sR, iR, _⟩ := VG.Proof.Pbkdf2.Md.Arm.Fin.wr_mem hp
  have ab := VG.Proof.Pbkdf2.Md.Arm.Fin.addr_blk hz hp
  have bS : Region.Sub ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀, H.N⟩ (VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀) := fun a h => VG.Proof.Pbkdf2.Md.Arm.Fin.blk_sub hp a (Region.sub_prefix (by omega_using [hB, hz_N64]) a h)
  have cS : Region.Sub ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.scA s₀, hH.stream.Wb⟩ (VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀) := Region.sub_prefix (by omega)
  have cB : Region.Disjoint ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀, H.N⟩ ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.scA s₀, hH.stream.Wb⟩ :=
    Offset.disjoint_base _ (by simp only [Hash.blkO, VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H]; omega_using [hwb]) (by simp only [Hash.blkO, VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H]; omega_using [nw, hf])
  exact
    { r0 := h0, r1 := h1, r12 := h12
      sp16 := by rw [hk.sp]; exact hp.sp16
      cw := by
        rw [hk.wr, ab, eS, eF]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact sub_of_self iR (Nat.le_refl _)
          · exact sub_of_off sR (by simp only [Hash.blkO, VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H]; omega)
          · exact sub_of_self (r := VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀) sR (by show hH.stream.Wb ≤ 8 * sc; omega)
      st_o := by rw [ab, eS, eF]; exact hp.i_s.sub_right bS
      st_sc := by rw [eS]; exact hp.i_s.sub_right cS
      o_sc := by rw [ab, eF]; exact cB
      b_st := by rw [below_eq hk.sp, eS]; exact hp.b_i
      b_o := by rw [below_eq hk.sp, ab, eF]; exact hp.b_s.sub_right bS
      b_sc := by rw [below_eq hk.sp]; exact hp.b_s.sub_right cS
      nst := by rw [eS]; exact hp.ni
      no := by rw [VG.Proof.Pbkdf2.Md.Arm.Fin.toNat_sO hp (by simp only [Hash.blkO, VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H]; omega_using [hB, hf]), eF]; simp only [Hash.blkO, VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H]; omega
      nsc := by omega }

/-- The call's arguments: the count still in `r2:r3`. -/
theorem fin1Args_ok {s : State} (hk : VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc s₀ s) (h0 : s.gpr .r0 = VG.Proof.Pbkdf2.Md.Arm.Fin.inn s₀) :
    WP isa (.block (([] : List Instr) ++ [] ++ scrAt .r1 H.blkO ++ ([.mov .r12 (.reg .r11)] : List Instr))) s
      fun t => VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc s₀ t ∧ FinArgs hH.stream t (VG.Proof.Pbkdf2.Md.Arm.Fin.inn s₀) (VG.Proof.Pbkdf2.Md.Arm.Fin.blk H s₀) (VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀) ∧ count t = count s ∧
        t.mem = s.mem := by
  have hf := hp.fits; have := hH.sizes.W
  simp only [List.nil_append]
  refine VG.Proof.Pbkdf2.Md.Arm.scrAt_ok (by simp only [Hash.blkO, VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H]; have := hH.sizes.N64; have := hH.B_le; omega)
    fun s₁ g₁ d₁ m₁ rd₁ wr₁ sp₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => WP.block_nil ?_
  have k₁ : VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc s₀ s₁ := hk.keep rd₁ wr₁ sp₁ (fun r hr => g₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    (rs := []) (by rw [m₁]; exact Frame.refl _ _) (by simp) (by simp)
  have k₂ : VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc s₀ s₂ := k₁.upd (by decide) u₂
  refine ⟨k₂, VG.Proof.Pbkdf2.Md.Arm.Fin.finArgs hH hp k₂ ?_ ?_ ?_, ?_, by rw [u₂.mem, m₁]⟩
  · rw [u₂.other _ (by decide), g₁ _ (by decide) (by decide), h0]
  · rw [u₂.other _ (by decide), d₁, hk.r11]
  · rw [u₂.gpr, g₁ _ (by decide) (by decide), hk.r11]
  · simp only [count, u₂.other _ (show Reg.r2 ≠ .r12 by decide), g₁ _ (show Reg.r2 ≠ .r1 by decide)
      (show Reg.r2 ≠ .r12 by decide), u₂.other _ (show Reg.r3 ≠ .r12 by decide),
      g₁ _ (show Reg.r3 ≠ .r1 by decide) (show Reg.r3 ≠ .r12 by decide)]

theorem finCall_ok {t : State} (hk : VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc s₀ t) (ha : FinArgs hH.stream t (VG.Proof.Pbkdf2.Md.Arm.Fin.inn s₀) (VG.Proof.Pbkdf2.Md.Arm.Fin.blk H s₀) (VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀))
    {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc s₀ s' →
      Frame [VG.Proof.Pbkdf2.Md.Arm.Fin.inR H s₀, ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀, H.N⟩, ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.scA s₀, hH.stream.Wb⟩, below s₀] t.mem s'.mem →
      (∀ m, hH.SH.Repr t.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.Fin.inn s₀)) m → m.length < 2 ^ 64 → count t = BitVec.ofNat 64 m.length →
        bytesAt s'.mem (VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀) H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.frame (.push Pbkdf2.Stream.Arm.fin2) (.call H.st.finN H.st.finC) (.pop .r1 8)) t Q :=
  fin_frame hH.stream ha fun s' ha' hpost => by
    have hz := hH.sizes
    have hz_W := hz.W; have := hH.stream.hWb; have hz_DN := hz.DN; have hz_NL := hz.NL; have hfi := hp.fits
    rw [VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H] at hfi
    have ab := VG.Proof.Pbkdf2.Md.Arm.Fin.addr_blk hz hp
    have f := ha'.frame
    rw [below_eq hk.sp, ab, hz.S, hz.F] at f
    rw [ab, hz.F] at hpost
    have cS : Region.Sub ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.scA s₀, hH.stream.Wb⟩ ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.scA s₀, 8 * H.st.W⟩ := Region.sub_prefix (by omega)
    have sd := VG.Proof.Pbkdf2.Md.Arm.Fin.save_disj hz hp
    refine hQ s' (hk.keep ha'.rd ha'.wr ha'.sp (fun r hr => ha'.cs r (VG.Proof.Pbkdf2.Md.Arm.Fin.kregs_pres r hr).1 (VG.Proof.Pbkdf2.Md.Arm.Fin.kregs_pres r hr).2) f
      ?_ ?_) f fun m hr hl hc => ?_
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r ((rfl | rfl | rfl) | rfl)
      · exact sd _ (by simp)
      · exact (sd _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))).sub_right
          (Offset.sub _ (by simp only [Hash.hvO, Hash.blkO]; omega) (by simp only [Hash.hvO, Hash.blkO]; omega))
      · exact (sd _ (by simp)).sub_right cS
      · exact sd _ (by simp)
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r ((rfl | rfl | rfl) | rfl)
      · exact ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.inR H s₀, by simp, fun _ h => h⟩
      · exact ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀, by simp, fun a h => VG.Proof.Pbkdf2.Md.Arm.Fin.blk_sub hp a (Region.sub_prefix (by omega) a h)⟩
      · exact ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀, by simp, Region.sub_prefix (by have hp_fits := hp.fits; rw [VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H] at hp_fits; omega)⟩
      · exact ⟨below s₀, by simp, fun _ h => h⟩
    · rw [bytesAt_take _ _ hz.DN]; exact hpost m hr hl hc

end

/-! ## The outer hash value and the padding -/

/-- The registers during the outer hash. -/
structure KR' (H : Hash) (sc : Nat) (s₀ s : State) : Prop extends VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc s₀ s where
  r0 : s.gpr .r0 = VG.Proof.Pbkdf2.Md.Arm.Fin.hv H s₀
  r3 : s.gpr .r3 = VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀
  r6 : s.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.Fin.blk H s₀

section
variable {H : Hash} {sc : Nat} (hz : VG.Proof.Pbkdf2.Md.Arm.Sizes H) {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.Arm.Fin.Pre H sc s₀)
include hz hp

omit hz in
/-- What the outer hash writes: the hash value being compressed and the block. -/
theorem hb_sub : Region.Sub ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.hvA H s₀, H.N + H.B⟩ (VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀) := by
  have hp_fits := hp.fits; exact VG.Proof.Pbkdf2.Md.Arm.Fin.scr_sub (by simp only [Hash.hvO]; omega)

theorem hb_kr : ∀ r ∈ [(⟨VG.Proof.Pbkdf2.Md.Arm.Fin.hvA H s₀, H.N + H.B⟩ : Region)], (saveR H.st (VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀)).Disjoint r ∧
    ∃ r' ∈ [VG.Proof.Pbkdf2.Md.Arm.Fin.inR H s₀, VG.Proof.Pbkdf2.Md.Arm.Fin.opR H s₀, VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀, below s₀], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.save_disj hz hp _ (by simp), VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀, by simp, VG.Proof.Pbkdf2.Md.Arm.Fin.hb_sub hp⟩

theorem mid_ok {md : Md H.B H.N H.L} (hR : md.Reloc)
    (hlen : VG.Proof.Pbkdf2.Md.Arm.wordsBytes (lenWords H.be H.L (H.B + H.D)) = md.lenBytes (H.B + H.D)) {s : State}
    (hk : VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc s₀ s) :
    WP isa (.block H.finMid) s fun s' => VG.Proof.Pbkdf2.Md.Arm.Fin.KR' H sc s₀ s' ∧ Frame [⟨VG.Proof.Pbkdf2.Md.Arm.Fin.hvA H s₀, H.N + H.B⟩] s.mem s'.mem ∧
      md.stateAt s'.mem (VG.Proof.Pbkdf2.Md.Arm.Fin.hvA H s₀) = md.stateAt s₀.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.Fin.outer s₀)) ∧
      bytesAt s'.mem (VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀) H.D = bytesAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀) H.D ∧
      bytesAt s'.mem (VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.D) = md.tailPad H.D := by
  have hz_N64 := hz.N64; have hp_fits := hp.fits; have hz_DN := hz.DN; have hz_pad := hz.pad; have hz_NL := hz.NL; have hz_D4 := hz.D4; have hz_L4 := hz.L4
  have hz_L16 := hz.L16; have hp_nw := hp.nw; have hp_no := hp.no; have hz_W := hz.W; have hz_N4 := hz.N4
  have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega_using [h]
  have hB4 : H.B % 4 = 0 := by rcases hz.B with h | h <;> omega_using [h]
  have hn : 4 * (H.N / 4) = H.N := by omega_using [hz_N4]
  have ablk := VG.Proof.Pbkdf2.Md.Arm.Fin.addr_blk hz hp; have ahv := VG.Proof.Pbkdf2.Md.Arm.Fin.addr_hv hz hp
  have tb : (VG.Proof.Pbkdf2.Md.Arm.Fin.blk H s₀).toNat = (VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀).toNat + H.blkO := VG.Proof.Pbkdf2.Md.Arm.Fin.toNat_sO hp (by simp only [Hash.blkO]; omega_using [hz_pad, hp_fits])
  have th : (VG.Proof.Pbkdf2.Md.Arm.Fin.hv H s₀).toNat = (VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀).toNat + H.hvO := VG.Proof.Pbkdf2.Md.Arm.Fin.toNat_sO hp (by simp only [Hash.hvO]; omega_using [hz_pad, hp_fits])
  obtain ⟨sR, _, _⟩ := VG.Proof.Pbkdf2.Md.Arm.Fin.wr_mem hp
  unfold Hash.finMid Hash.pad Hash.atHv
  simp only [List.append_assoc, List.singleton_append]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  refine VG.Proof.Pbkdf2.Md.Arm.scrAt_ok (by simp only [Hash.hvO, VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H]; omega_using [hz_W]) fun s₂ g₂ d₂ m₂ rd₂ wr₂ sp₂ =>
    VG.Proof.Pbkdf2.Md.Arm.scrAt_ok (by simp only [Hash.blkO, VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H]; omega_using [hz_W, hz_N64]) fun s₃ g₃ d₃ m₃ rd₃ wr₃ sp₃ => ?_
  have r11₁ : s₁.gpr .r11 = VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀ := by rw [u₁.other _ (by decide), hk.r11]
  have r0₃ : s₃.gpr .r0 = VG.Proof.Pbkdf2.Md.Arm.Fin.hv H s₀ := by rw [g₃ _ (by decide) (by decide), d₂, r11₁]
  have r6₃ : s₃.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.Fin.blk H s₀ := by rw [d₃, g₂ _ (by decide) (by decide), r11₁]
  have r5₃ : s₃.gpr .r5 = VG.Proof.Pbkdf2.Md.Arm.Fin.outer s₀ := by
    rw [g₃ _ (by decide) (by decide), g₂ _ (by decide) (by decide), u₁.other _ (by decide), hk.r5]
  have k₃ : VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc s₀ s₃ := (hk.upd (by decide) u₁).keep (by rw [rd₃, rd₂]) (by rw [wr₃, wr₂])
    (by rw [sp₃, sp₂]) (fun r hr => by
      have : r ≠ .r0 ∧ r ≠ .r6 ∧ r ≠ .r12 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide
      rw [g₃ r this.2.1 this.2.2, g₂ r this.1 this.2.2]) (rs := []) (by rw [m₃, m₂]; exact Frame.refl _ _)
      (by simp) (by simp)
  have oR : VG.Proof.Pbkdf2.Md.Arm.Fin.outerR H s₀ ∈ s₃.rd ++ s₃.wr := by rw [k₃.rd, hp.rd]; simp
  refine VG.Proof.Pbkdf2.Md.Arm.copyW_ok (by decide) (by decide) 0 0 (H.N / 4) ⟨by omega_using [hz_N64], by omega⟩ _ s₃ _
    (by rw [r5₃]; omega_using [hp_no]) (by rw [r0₃, th]; simp only [Hash.hvO]; omega_using [hp_nw, hp_fits])
    (fun j hj => ?_) (fun j hj => ?_) ?_ fun s₄ g₄ rd₄ wr₄ sp₄ m₄ => ?_
  · rw [r5₃, VG.Proof.Pbkdf2.Md.Arm.Fin.add0]; exact ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.outerR H s₀, oR, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj, hz_N64])⟩
  · rw [r0₃, ahv, k₃.wr, VG.Proof.Pbkdf2.Md.Arm.Fin.add0, show VG.Proof.Pbkdf2.Md.Arm.Fin.hvA H s₀ = VG.Proof.Pbkdf2.Md.Arm.Fin.scA s₀ + BitVec.ofNat 64 H.hvO from rfl, Memory.add_ofNat]
    exact VG.Proof.Pbkdf2.Md.Arm.Fin.in_scr hp rfl (by simp only [Hash.hvO]; omega_using [hj, hp_fits])
  · rw [r5₃, r0₃, ahv, VG.Proof.Pbkdf2.Md.Arm.Fin.add0, VG.Proof.Pbkdf2.Md.Arm.Fin.add0, hn]
    exact hp.o_s.sep (Memory.contains_base (by omega_using [])) (Offset.contains_base _ (by simp only [Hash.hvO]; omega_using [hp_fits])
      (by simp only [Hash.hvO]; omega_using [hp_nw, hp_fits]))
  rw [r0₃, ahv, r5₃, VG.Proof.Pbkdf2.Md.Arm.Fin.add0, VG.Proof.Pbkdf2.Md.Arm.Fin.add0, hn] at m₄
  have g6 : s₄.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.Fin.blk H s₀ := by rw [g₄ _ (by decide), r6₃]
  refine VG.Proof.Pbkdf2.Md.Arm.padFrom_ok (a := H.D) (b := H.B - H.L) (by omega) (by omega_using [hB4, hz_L4, hz_D4]) (by omega_using [hB]) (s := s₄) (p := VG.Proof.Pbkdf2.Md.Arm.Fin.blk H s₀) g6
    (by rw [tb]; simp only [Hash.blkO]; omega_using [hp_nw, hp_fits])
    (fun j hj => by rw [ablk]; exact VG.Proof.Pbkdf2.Md.Arm.Fin.in_blk hp (wr₄.trans k₃.wr) (by omega_using [hj])) fun s₅ g₅ rd₅ wr₅ sp₅ m₅ => ?_
  rw [ablk] at m₅
  have lw := HashOK.lenWords_length (H := H)
  rw [← List.append_nil (constW (H.B - H.L) (lenWords H.be H.L (H.B + H.D)))]
  refine VG.Proof.Pbkdf2.Md.Arm.constW_ok (p := VG.Proof.Pbkdf2.Md.Arm.Fin.blk H s₀) (lenWords H.be H.L (H.B + H.D)) (H.B - H.L) (by rw [lw]; omega_using [hB, hz_pad])
    (by rw [lw, tb]; simp only [Hash.blkO]; omega_using [hp_nw, hz_pad, hp_fits]) _ s₅ _ (by rw [g₅ _ (by decide), g6])
    (fun j hj => by rw [lw] at hj; rw [ablk]; exact VG.Proof.Pbkdf2.Md.Arm.Fin.in_blk hp (wr₅.trans (wr₄.trans k₃.wr)) (by omega_using [hj, hz_pad]))
    fun s₆ g₆ rd₆ wr₆ sp₆ m₆ => WP.block_nil ?_
  rw [ablk, hlen] at m₆
  have lpz : ([0x80] ++ List.replicate (H.B - H.L - H.D - 1) 0 : List Byte).length = H.B - H.L - H.D := by
    simp; omega_using [hz_pad]
  have hM : s₆.mem = VG.WriteBytes.writeBytes (VG.WriteBytes.writeBytes (VG.WriteBytes.writeBytes s₃.mem (VG.Proof.Pbkdf2.Md.Arm.Fin.hvA H s₀) (bytesAt s₃.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.Fin.outer s₀)) H.N))
      (VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀ + BitVec.ofNat 64 H.D) ([0x80] ++ List.replicate (H.B - H.L - H.D - 1) 0))
      (VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀ + BitVec.ofNat 64 (H.B - H.L)) (md.lenBytes (H.B + H.D)) := by
    rw [m₆, m₅, m₄]
  have hG : ∀ r, r ≠ .r12 → s₆.gpr r = s₃.gpr r := fun r hr => by rw [g₆ r hr, g₅ r hr, g₄ r hr]
  have eb : VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀ = VG.Proof.Pbkdf2.Md.Arm.Fin.hvA H s₀ + BitVec.ofNat 64 H.N := by
    rw [VG.Proof.Pbkdf2.Md.Arm.Fin.hvA, VG.Proof.Pbkdf2.Md.Arm.Fin.blkA, Memory.add_ofNat]; rfl
  have fM : Frame [⟨VG.Proof.Pbkdf2.Md.Arm.Fin.hvA H s₀, H.N + H.B⟩] s₃.mem s₆.mem := by
    rw [hM]
    refine ((VG.WriteBytes.writeBytes_frame _ _ _ ?_).trans (VG.WriteBytes.writeBytes_frame _ _ _ ?_)).trans (VG.WriteBytes.writeBytes_frame _ _ _ ?_)
    · rw [bytesAt_length]; exact Memory.contains_base (by omega)
    · rw [lpz, eb, Memory.add_ofNat]; exact Offset.contains_base _ (by omega_using [hz_pad]) (by omega_using [hz_DN, hz_N64])
    · rw [md.lenBytes_length, eb, Memory.add_ofNat]; exact Offset.contains_base _ (by omega_using [hz_pad]) (by omega_using [hp_nw, hp_fits])
  have m₃' : s₃.mem = s.mem := by rw [m₃, m₂, u₁.mem]
  have S1 : Mem.Sep (VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀) H.D (VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.L - H.D) := by
    have := Offset.sep (VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀) (d := 0) (n := H.D) (e := H.D) (k := H.B - H.L - H.D) (.inl (by omega))
      (by omega_using [hz_DN, hz_N64]) (by omega_using [hp_nw, hz_DN, hp_fits])
    rwa [VG.Proof.Pbkdf2.Md.Arm.Fin.add0] at this
  have S2 : ∀ {a n : Nat}, a + n ≤ H.B - H.L →
      Mem.Sep (VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀ + BitVec.ofNat 64 a) n (VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀ + BitVec.ofNat 64 (H.B - H.L)) H.L :=
    fun h' => Offset.sep _ (.inl h') (by omega_using [h', hp_nw, hp_fits]) (by omega_using [hp_nw, hz_pad, hp_fits])
  have S3 : Mem.Sep (VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀) H.D (VG.Proof.Pbkdf2.Md.Arm.Fin.hvA H s₀) H.N := by
    have := Offset.sep (VG.Proof.Pbkdf2.Md.Arm.Fin.hvA H s₀) (d := H.N) (n := H.D) (e := 0) (k := H.N) (.inr (by omega)) (by omega_using [hz_DN, hz_N64]) (by omega_using [hz_N64])
    rwa [VG.Proof.Pbkdf2.Md.Arm.Fin.add0, ← eb] at this
  have f₄₆ : Frame [⟨VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀, H.B⟩] s₄.mem s₆.mem := by
    rw [m₆, m₅]
    refine (VG.WriteBytes.writeBytes_frame _ _ _ ?_).trans (VG.WriteBytes.writeBytes_frame _ _ _ ?_)
    · rw [lpz]; exact Offset.contains_base _ (by omega_using [hz_pad]) (by omega_using [hz_DN, hz_N64])
    · rw [md.lenBytes_length]; exact Offset.contains_base _ (by omega_using [hz_pad]) (by omega_using [hp_nw, hp_fits])
  have dHB : Region.Disjoint ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.hvA H s₀, H.N⟩ ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀, H.B⟩ :=
    Offset.disjoint _ (.inl (by simp only [Hash.hvO, Hash.blkO]; omega)) (by simp only [Hash.hvO]; omega_using [hp_nw, hp_fits])
      (by simp only [Hash.blkO]; omega_using [hp_nw, hp_fits])
  refine ⟨⟨k₃.keep (by rw [rd₆, rd₅, rd₄]) (by rw [wr₆, wr₅, wr₄]) (by rw [sp₆, sp₅, sp₄]) (fun r hr => hG r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      fM (fun r hr => (VG.Proof.Pbkdf2.Md.Arm.Fin.hb_kr hz hp r hr).1) (fun r hr => (VG.Proof.Pbkdf2.Md.Arm.Fin.hb_kr hz hp r hr).2),
    by rw [hG _ (by decide), r0₃], by rw [hG _ (by decide), g₃ _ (by decide) (by decide),
      g₂ _ (by decide) (by decide), u₁.gpr, hk.r11], by rw [hG _ (by decide), r6₃]⟩,
    m₃' ▸ fM, ?_, ?_, ?_⟩
  · refine hR _ _ _ _ fun i hi => ?_
    rw [f₄₆.bytes (R := ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.hvA H s₀, H.N⟩) (fun r hr => by simp at hr; subst hr; exact dHB) (by show H.N ≤ 2 ^ 64; omega_using [hz_N64]) hi, m₄,
      writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega_using [hz_N64]),
      bytesAt_getD' _ _ hi]
    exact k₃.frame.bytes (R := VG.Proof.Pbkdf2.Md.Arm.Fin.outerR H s₀) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      · exact hp.i_o.symm
      · exact hp.o_p
      · exact hp.o_s
      · exact hp.b_o.symm) (by show H.N + H.B ≤ 2 ^ 64; omega_using [hp_nw, hp_fits]) (by show i < H.N + H.B; omega_using [hi])
  · rw [hM, bytesAt_writeBytes_sep _ _ (by
        rw [md.lenBytes_length]; have := S2 (a := 0) (n := H.D) (by omega_using [hz_pad]); rwa [VG.Proof.Pbkdf2.Md.Arm.Fin.add0] at this) (by omega),
      bytesAt_writeBytes_sep _ _ (by rw [lpz]; exact S1) (by omega_using [hz_DN, hz_N64]),
      bytesAt_writeBytes_sep _ _ (by rw [bytesAt_length]; exact S3) (by omega), m₃']
  · rw [show H.B - H.D = (H.B - H.L - H.D) + H.L by omega_using [hz_pad], bytesAt_add, Memory.add_ofNat (VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀),
      show H.D + (H.B - H.L - H.D) = H.B - H.L by omega_using [hz_pad], hM,
      bytesAt_writeBytes_self' (md.lenBytes_length _) (by omega_using [hz_L16]),
      bytesAt_writeBytes_sep _ _ (by rw [md.lenBytes_length]; exact S2 (by omega_using [hz_pad])) (by omega_using [hp_nw, hp_fits]),
      bytesAt_writeBytes_self' lpz (by omega), Md.tailPad, show H.B - H.L - 1 - H.D = H.B - H.L - H.D - 1 by omega_using []]

end

/-! ## The compression and the MAC -/

section
variable {H : Hash} {sc : Nat} (hz : VG.Proof.Pbkdf2.Md.Arm.Sizes H) {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.Arm.Fin.Pre H sc s₀)
include hz hp

/-- What the call of the compression function needs. -/
theorem callOk_of {s : State} (h : VG.Proof.Pbkdf2.Md.Arm.Fin.KR' H sc s₀ s) :
    VG.Proof.Pbkdf2.Md.Arm.CallOk s H.N H.B H.so (VG.Proof.Pbkdf2.Md.Arm.Fin.hv H s₀) (VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀) (VG.Proof.Pbkdf2.Md.Arm.Fin.blk H s₀) := by
  have hz_N64 := hz.N64; have hp_fits := hp.fits; have hp_nw := hp.nw; have hz_so := hz.so; have hB := hz.B
  have hsc : VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀ ∈ s.wr := by simp [h.wr, hp.wr]
  rw [VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H] at *
  refine ⟨h.r0, h.r3, h.r6, by rw [VG.Proof.Pbkdf2.Md.Arm.Fin.toNat_sO hp (by simp only [Hash.hvO, VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H]; omega)]; simp only [Hash.hvO, VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H]; omega,
    by rw [VG.Proof.Pbkdf2.Md.Arm.Fin.toNat_sO hp (by simp only [Hash.blkO, VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H]; omega)]; simp only [Hash.blkO, VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H]; omega,
    by omega, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [VG.Proof.Pbkdf2.Md.Arm.Fin.addr_hv hz hp, VG.Proof.Pbkdf2.Md.Arm.Fin.addr_blk hz hp, VG.Proof.Pbkdf2.Md.Arm.Fin.hvA, VG.Proof.Pbkdf2.Md.Arm.Fin.blkA, Hash.hvO, Hash.blkO, VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H]
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · refine Covers.of_sub fun r hr => ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀, List.mem_append_right _ hsc, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, rfl, by dsimp only; omega⟩
    · exact ⟨_, rfl, by dsimp only; omega⟩
    · exact ⟨0, by simp, by dsimp only; omega⟩
  · refine Covers.of_sub fun r hr => ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀, hsc, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, rfl, by dsimp only; omega⟩
    · exact ⟨0, by simp, by dsimp only; omega⟩

/-- The compression of the block into the outer hash value. -/
theorem cmp_ok {md : Md H.B H.N H.L} (hf : VG.Proof.Pbkdf2.Md.Arm.CompOk md H.so H.compC) {s : State} (h : VG.Proof.Pbkdf2.Md.Arm.Fin.KR' H sc s₀ s)
    {Q : State → Prop}
    (k : ∀ s', VG.Proof.Pbkdf2.Md.Arm.Fin.KR' H sc s₀ s' → Frame [⟨VG.Proof.Pbkdf2.Md.Arm.Fin.hvA H s₀, H.N⟩, ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.scA s₀, H.so⟩] s.mem s'.mem →
      md.stateAt s'.mem (VG.Proof.Pbkdf2.Md.Arm.Fin.hvA H s₀) = md.compress (md.stateAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Fin.hvA H s₀)) (md.blockAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀)) →
      Q s') :
    WP isa H.compressBlock s Q := by
  have hz_N64 := hz.N64; have hp_fits := hp.fits; have hz_so := hz.so; have hz_W := hz.W
  have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  refine VG.Proof.Pbkdf2.Md.Arm.compressBlock_ok hf (VG.Proof.Pbkdf2.Md.Arm.Fin.callOk_of hz hp h) fun s' hrd hwr hcs h0 h3 hsp hfr hst => ?_
  rw [VG.Proof.Pbkdf2.Md.Arm.Fin.addr_hv hz hp] at hfr
  rw [VG.Proof.Pbkdf2.Md.Arm.Fin.addr_hv hz hp, VG.Proof.Pbkdf2.Md.Arm.Fin.addr_blk hz hp] at hst
  have sd := VG.Proof.Pbkdf2.Md.Arm.Fin.save_disj hz hp
  rw [VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H] at *
  refine k s' ⟨h.toKR.keep hrd hwr hsp (fun r hr => hcs r (VG.Proof.Pbkdf2.Md.Arm.Fin.kregs_pres r hr).1 (VG.Proof.Pbkdf2.Md.Arm.Fin.kregs_pres r hr).2) hfr ?_ ?_,
    h0, h3, (hcs _ (by decide) (by decide)).trans h.r6⟩ hfr hst
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact (sd _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))).sub_right (Region.sub_prefix (by omega))
    · exact (sd ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.scA s₀, 8 * H.st.W⟩ (List.mem_cons_self ..)).sub_right (Region.sub_prefix (by omega))
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀, by simp, VG.Proof.Pbkdf2.Md.Arm.Fin.scr_sub (by simp only [Hash.hvO, VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H]; omega)⟩
    · exact ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.scR sc s₀, by simp, Region.sub_prefix (by omega)⟩

/-- The MAC to `out`, and our caller's registers back. -/
theorem out_ok {md : Md H.B H.N H.L} (ho : VG.Proof.Pbkdf2.Md.Arm.OutOk md H.out) {s : State} (h : VG.Proof.Pbkdf2.Md.Arm.Fin.KR' H sc s₀ s) :
    WP isa (.block H.finOut) s fun s' => abiPreserved s₀ s' ∧
      bytesAt s'.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.Fin.op s₀)) H.D = (md.digest (md.stateAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Fin.hvA H s₀))).take H.D := by
  have hz_N64 := hz.N64; have hp_fits := hp.fits; have hz_DN := hz.DN; have hz_D4 := hz.D4; have hz_W := hz.W; have hp_nw := hp.nw; have hp_np := hp.np
  have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  have hD4 : 4 * (H.D / 4) = H.D := by omega
  have ahv := VG.Proof.Pbkdf2.Md.Arm.Fin.addr_hv hz hp; have ablk := VG.Proof.Pbkdf2.Md.Arm.Fin.addr_blk hz hp
  have th : (VG.Proof.Pbkdf2.Md.Arm.Fin.hv H s₀).toNat = (VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀).toNat + H.hvO := VG.Proof.Pbkdf2.Md.Arm.Fin.toNat_sO hp (by simp only [Hash.hvO]; omega)
  have tb : (VG.Proof.Pbkdf2.Md.Arm.Fin.blk H s₀).toNat = (VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀).toNat + H.blkO := VG.Proof.Pbkdf2.Md.Arm.Fin.toNat_sO hp (by simp only [Hash.blkO]; omega)
  obtain ⟨sR, _, pR⟩ := VG.Proof.Pbkdf2.Md.Arm.Fin.wr_mem hp
  have hdl := md.digest_length (md.stateAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Fin.hvA H s₀))
  -- The restore, after code that writes `out` and maybe the block.
  have fin : ∀ s₁ : State, s₁.gpr .r11 = VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀ → s₁.rd = s.rd → s₁.wr = s.wr → s₁.sp = s.sp →
      SavedRegs H.st (VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀) s₀ s₁.mem →
      bytesAt s₁.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.Fin.op s₀)) H.D = (md.digest (md.stateAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Fin.hvA H s₀))).take H.D →
      WP isa (.block H.st.restore) s₁ fun s' => abiPreserved s₀ s' ∧
        bytesAt s'.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.Fin.op s₀)) H.D = (md.digest (md.stateAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Fin.hvA H s₀))).take H.D := by
    intro s₁ h11 hrd hwr hsp hsv hb
    have hfi := hp.fits; rw [VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H] at hfi
    exact WP.mono (Pbkdf2.Stream.Arm.restore_ok H.st h11 hz.W hsv (by rw [hwr, h.wr, hp.wr]; simp) (L := 8 * sc)
      (by omega_using [hfi]) hp.nw) fun s' ⟨hm, _, _, hsp', hg, _⟩ =>
        ⟨⟨fun r hr => hg r (preserved_saved r hr), by rw [hsp', hsp, h.sp]⟩, by rw [hm]; exact hb⟩
  have sdisj : ∀ {R : Region}, R ∈ [VG.Proof.Pbkdf2.Md.Arm.Fin.opR H s₀, ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀, H.N⟩] → (saveR H.st (VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀)).Disjoint R := by
    intro R hR
    have sd := VG.Proof.Pbkdf2.Md.Arm.Fin.save_disj hz hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact sd _ (by simp)
    · have hfi := hp.fits; rw [VG.Proof.Pbkdf2.Md.Arm.Fin.buf_eq H] at hfi
      exact (sd _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))).sub_right
        (Offset.sub _ (by simp only [Hash.hvO, Hash.blkO]; omega_using []) (by simp only [Hash.hvO, Hash.blkO]; omega_using [hB, hz_N64]))
  unfold Hash.finOut
  by_cases hDN : H.D < H.N
  · simp only [hDN, ↓reduceIte, List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (ho s ?_ ?_ ?_ ?_ ?_) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, m₁⟩ => ?_
    · rw [h.r0, th]; simp only [Hash.hvO]; omega_using [hp_nw, hp_fits]
    · rw [h.r6, tb]; simp only [Hash.blkO]; omega_using [hB, hp_nw, hp_fits, hz_N64]
    · rw [h.r0, ahv]; exact VG.Proof.Pbkdf2.Md.Arm.Fin.in_scr' hp h.wr (by simp only [Hash.hvO]; omega_using [hp_fits])
    · rw [h.r6, ablk]; exact VG.Proof.Pbkdf2.Md.Arm.Fin.in_scr hp h.wr (by simp only [Hash.blkO]; omega_using [hB, hp_fits, hz_N64])
    · rw [h.r0, h.r6, ahv, ablk]; exact Offset.disjoint _ (.inl (by simp only [Hash.hvO, Hash.blkO]; omega))
        (by simp only [Hash.hvO]; omega_using [hp_nw, hp_fits]) (by simp only [Hash.blkO]; omega_using [hp_nw, hp_fits])
    rw [h.r6, ablk, h.r0, ahv] at m₁
    have g6 : s₁.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.Fin.blk H s₀ := by rw [g₁ _ (by decide) (by decide), h.r6]
    have g7 : s₁.gpr .r7 = VG.Proof.Pbkdf2.Md.Arm.Fin.op s₀ := by rw [g₁ _ (by decide) (by decide), h.r7]
    refine VG.Proof.Pbkdf2.Md.Arm.copyW_ok (by decide) (by decide) 0 0 (H.D / 4) ⟨by omega_using [hz_DN, hz_N64], by omega⟩ _ s₁ _
      (by rw [g6, tb]; simp only [Hash.blkO]; omega) (by rw [g7]; omega)
      (fun j hj => ?_) (fun j hj => ?_) ?_ fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
    · rw [g6, ablk, rd₁, wr₁, VG.Proof.Pbkdf2.Md.Arm.Fin.add0]
      obtain ⟨r, hr, hc⟩ := VG.Proof.Pbkdf2.Md.Arm.Fin.in_blk hp h.wr (a := 4 * j) (n := 4) (by omega_using [hj, hB, hz_DN, hz_N64])
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [g7, wr₁, h.wr, VG.Proof.Pbkdf2.Md.Arm.Fin.add0]; exact ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.opR H s₀, pR, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj, hz_DN, hz_N64])⟩
    · rw [g6, g7, ablk, VG.Proof.Pbkdf2.Md.Arm.Fin.add0, VG.Proof.Pbkdf2.Md.Arm.Fin.add0, hD4]
      exact (hp.p_s.sub_right (fun a ha => VG.Proof.Pbkdf2.Md.Arm.Fin.blk_sub hp a (Region.sub_prefix (by omega_using [hB, hz_DN, hz_N64]) a ha))).symm.sep
        (Region.contains_self _ _) (Region.contains_self _ _)
    rw [g7, g6, ablk, VG.Proof.Pbkdf2.Md.Arm.Fin.add0, VG.Proof.Pbkdf2.Md.Arm.Fin.add0, hD4] at m₂
    have f₁ : Frame [⟨VG.Proof.Pbkdf2.Md.Arm.Fin.blkA H s₀, H.N⟩] s.mem s₁.mem := by
      rw [m₁]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hdl]; exact Region.contains_self _ _)
    have f₂ : Frame [VG.Proof.Pbkdf2.Md.Arm.Fin.opR H s₀] s₁.mem s₂.mem := by
      rw [m₂]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
    refine fin s₂ (by rw [g₂ _ (by decide), g₁ _ (by decide) (by decide), h.r11]) (rd₂.trans rd₁)
      (wr₂.trans wr₁) (sp₂.trans sp₁) ((h.saved.frame H.st f₁ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact sdisj (by simp)).frame H.st f₂ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact sdisj (by simp)) ?_
    rw [m₂, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega_using [hz_DN, hz_N64]), bytesAt_take _ _ hz.DN, m₁,
      bytesAt_writeBytes_self' hdl (by omega)]
  · simp only [hDN, ↓reduceIte, List.cons_append]
    have eDN : H.D = H.N := by omega_using [hDN, hz_DN]
    refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (ho s₁ ?_ ?_ ?_ ?_ ?_) fun s₂ ⟨g₂, rd₂, wr₂, sp₂, m₂⟩ => ?_
    · rw [u₁.other _ (by decide), h.r0, th]; simp only [Hash.hvO]; omega_using [hp_nw, hp_fits]
    · rw [u₁.gpr, h.r7, ← eDN]; omega
    · rw [u₁.other _ (by decide), h.r0, ahv, u₁.rd, u₁.wr]; exact VG.Proof.Pbkdf2.Md.Arm.Fin.in_scr' hp h.wr (by simp only [Hash.hvO]; omega_using [hp_fits])
    · rw [u₁.gpr, h.r7, u₁.wr, h.wr, ← eDN]; exact ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.opR H s₀, pR, Region.contains_self _ _⟩
    · rw [u₁.other _ (by decide), u₁.gpr, h.r0, h.r7, ahv, ← eDN]
      exact (hp.p_s.sub_right (VG.Proof.Pbkdf2.Md.Arm.Fin.scr_sub (by simp only [Hash.hvO]; omega_using [hz_DN, hp_fits]))).symm
    rw [u₁.gpr, h.r7, u₁.other _ (by decide), h.r0, ahv, u₁.mem] at m₂
    have f₂ : Frame [VG.Proof.Pbkdf2.Md.Arm.Fin.opR H s₀] s.mem s₂.mem := by
      rw [m₂]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hdl, ← eDN]; exact Region.contains_self _ _)
    refine fin s₂ (by rw [g₂ _ (by decide) (by decide), u₁.other _ (by decide), h.r11]) (rd₂.trans u₁.rd)
      (wr₂.trans u₁.wr) (sp₂.trans u₁.sp) (h.saved.frame H.st f₂ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact sdisj (by simp)) ?_
    rw [m₂, eDN, bytesAt_writeBytes_self' hdl (by omega_using [hz_N64]), List.take_of_length_le (by rw [hdl])]

end

/-! ## Correctness -/

theorem correct {H : Hash} (hH : VG.Proof.Pbkdf2.Md.Arm.HashOK H) {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.Arm.Fin.Pre H sc s₀) :
    WP isa H.hmacFin s₀ fun s' => abiPreserved s₀ s' ∧ (finG hH.SH sc).post s₀ s' := by
  have hz := hH.sizes
  have hz_N64 := hz.N64; have hz_DN := hz.DN; have hz_NL := hz.NL; have hp_fits := hp.fits
  have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  unfold Hash.hmacFin Impl.Pbkdf2.Stream.Arm.Hash.callFin
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.Arm.Fin.pro_ok hH hp) fun s₁ ⟨k₁, r0₁, c₁, f₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.Arm.Fin.fin1Args_ok hH hp k₁ r0₁) fun t₁ ⟨kt₁, a₁, ct₁, mt₁⟩ =>
    VG.Proof.Pbkdf2.Md.Arm.Fin.finCall_ok hH hp kt₁ a₁ fun s₂ k₂ _ d₂ => ?_))
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.Arm.Fin.mid_ok hz hp hH.reloc hH.len k₂) fun s₃ ⟨k₃, _, st₃, b₃, p₃⟩ => ?_)
  refine WP.seq (VG.Proof.Pbkdf2.Md.Arm.Fin.cmp_ok hz hp hH.comp k₃ fun s₄ k₄ _ e₄ => ?_)
  refine WP.mono (VG.Proof.Pbkdf2.Md.Arm.Fin.out_ok hz hp hH.out k₄) fun s' ⟨habi, hout⟩ => ⟨habi, ?_⟩
  intro k0 text hk0 hlen hrI hcnt hrO
  have hk0' : k0.length = H.B := by rw [hk0, hH.hB]
  have hl0 : (xorPad k0 ipad ++ text).length = H.B + text.length := by
    rw [List.length_append, VG.Proof.Hmac.Common.xorPad_length, hk0']
  -- The inner digest.
  have rI : hH.SH.Repr t₁.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.Fin.inn s₀)) (xorPad k0 ipad ++ text) := by
    rw [mt₁]
    refine Pbkdf2.Stream.Arm.repr_keep hH.stream f₁ (fun r hr => ?_) hrI
    simp only [List.mem_singleton] at hr; subst hr
    rw [hz.S]; exact (VG.Proof.Pbkdf2.Md.Arm.Fin.save_disj hz hp _ (by simp)).symm
  have dig := d₂ _ rI (by rw [hl0]; rw [hk0'] at hlen; exact hlen) (by rw [ct₁, c₁, hcnt, hl0, hH.hB])
  -- The outer hash.
  rw [st₃, VG.Proof.Pbkdf2.Md.Arm.blockAt_eq (by omega_using [hz_NL, hz_DN]) p₃, b₃, dig] at e₄
  show bytesAt s'.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.Fin.op s₀)) hH.SH.digestBytes = hmacBlockKey hH.SH.H k0 text
  rw [hH.hD, hout, e₄, Md.hmac_outer hH.link hk0 hrO]

end VG.Proof.Pbkdf2.Md.Arm.Fin

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.Arm.HmacFinCT`. -/
section

/-!
# HMAC's `finalize` over a Merkle–Damgård hash function on ARMv7: constant time

As for `iterate` (`IterateCT.lean`): we relate two runs (`RelCT`). Correctness
determines our registers from the public arguments alone, so the taint
analysis proves the blocks between the calls constant time from them
(`Checks`, evaluated for each hash function); the call of the streaming
`finalize` is constant time by its own proof (`fin_rel`,
`Proof/Pbkdf2/Stream/Arm/Hash.lean`), and the call of the compression function
by its own (`compressBlock_rel`).
-/

namespace VG.Proof.Pbkdf2.Md.Arm.Fin

open VG VG.Arm
open VG.Impl.Pbkdf2.Md.Arm (Hash)
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)
open VG.Proof.Pbkdf2.Md.Arm
open VG.Proof.Pbkdf2.Stream.Arm (finG count FinArgs fin_rel)

/-- The registers the blocks after the outer hash value is set up use. -/
abbrev regsO : List Reg := [.r0, .r3, .r5, .r6, .r7, .r11]

/-- The taint checks of the pieces of `finalize` between its calls, which
depend on the hash function's sizes, its length field and its digest. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (taint.check (argTaint [.r0, .r1, .r2, .r3] 8) (.block H.finPrologue) hc).isSome = true
  fin1 : ∃ hc, (taint.check (Taint.ofRegs VG.Proof.Pbkdf2.Md.Arm.Fin.kregs)
    (.block (([] : List Instr) ++ [] ++ scrAt .r1 H.blkO ++ [.mov .r12 (.reg .r11)])) hc).isSome = true
  mid : ∃ hc, (taint.check (Taint.ofRegs VG.Proof.Pbkdf2.Md.Arm.Fin.kregs) (.block H.finMid) hc).isSome = true
  out : ∃ hc, (taint.check (Taint.ofRegs VG.Proof.Pbkdf2.Md.Arm.Fin.regsO) (.block H.finOut) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  r0 : s₀.gpr .r0 = s₀'.gpr .r0
  r1 : s₀.gpr .r1 = s₀'.gpr .r1
  r2 : s₀.gpr .r2 = s₀'.gpr .r2
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  a0 : stackArg s₀ 0 = stackArg s₀' 0
  a1 : stackArg s₀ 1 = stackArg s₀' 1

section
variable {H : Hash} {sc : Nat} {s₀ s₀' : State}

theorem kr_agree (hq : VG.Proof.Pbkdf2.Md.Arm.Fin.PubEq s₀ s₀') {s s' : State} (h : VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc s₀ s) (h' : VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc s₀' s') :
    ∀ r ∈ VG.Proof.Pbkdf2.Md.Arm.Fin.kregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.r5, h'.r5, VG.Proof.Pbkdf2.Md.Arm.Fin.outer, VG.Proof.Pbkdf2.Md.Arm.Fin.outer, hq.r1]
  · rw [h.r7, h'.r7, VG.Proof.Pbkdf2.Md.Arm.Fin.op, VG.Proof.Pbkdf2.Md.Arm.Fin.op, hq.a0]
  · rw [h.r11, h'.r11, VG.Proof.Pbkdf2.Md.Arm.Fin.scr, VG.Proof.Pbkdf2.Md.Arm.Fin.scr, hq.a1]

theorem kr'_agree (hq : VG.Proof.Pbkdf2.Md.Arm.Fin.PubEq s₀ s₀') {s s' : State} (h : VG.Proof.Pbkdf2.Md.Arm.Fin.KR' H sc s₀ s) (h' : VG.Proof.Pbkdf2.Md.Arm.Fin.KR' H sc s₀' s') :
    ∀ r ∈ VG.Proof.Pbkdf2.Md.Arm.Fin.regsO, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.r0, h'.r0, VG.Proof.Pbkdf2.Md.Arm.Fin.hv, VG.Proof.Pbkdf2.Md.Arm.Fin.hv, VG.Proof.Pbkdf2.Md.Arm.Fin.scr, VG.Proof.Pbkdf2.Md.Arm.Fin.scr, hq.a1]
  · rw [h.r3, h'.r3, VG.Proof.Pbkdf2.Md.Arm.Fin.scr, VG.Proof.Pbkdf2.Md.Arm.Fin.scr, hq.a1]
  · exact VG.Proof.Pbkdf2.Md.Arm.Fin.kr_agree hq h.toKR h'.toKR _ (by simp)
  · rw [h.r6, h'.r6, VG.Proof.Pbkdf2.Md.Arm.Fin.blk, VG.Proof.Pbkdf2.Md.Arm.Fin.blk, VG.Proof.Pbkdf2.Md.Arm.Fin.scr, VG.Proof.Pbkdf2.Md.Arm.Fin.scr, hq.a1]
  · exact VG.Proof.Pbkdf2.Md.Arm.Fin.kr_agree hq h.toKR h'.toKR _ (by simp)
  · exact VG.Proof.Pbkdf2.Md.Arm.Fin.kr_agree hq h.toKR h'.toKR _ (by simp)

/-- Code the taint analysis checks from the registers `rs`, in two runs
whose single-run facts `F` and `F'` agree on them. -/
theorem rel_regs {F F' G G' : State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s s', F s → F' s' → ∀ r ∈ rs, s.gpr r = s'.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s s' h => Taint.agree_ofRegs (hag s s' h.1 h.2)) hc).wp
    fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

end

theorem fin_ct {H : Hash} (hH : VG.Proof.Pbkdf2.Md.Arm.HashOK H) (hc : VG.Proof.Pbkdf2.Md.Arm.Fin.Checks H) {sc : Nat} {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Md.Arm.Fin.Pre H sc s₀)
    (hp' : VG.Proof.Pbkdf2.Md.Arm.Fin.Pre H sc s₀') (hq : VG.Proof.Pbkdf2.Md.Arm.Fin.PubEq s₀ s₀') :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacFin fun _ _ => True := by
  have hz := hH.sizes
  have e : VG.Proof.Pbkdf2.Md.Arm.Fin.inn s₀' = VG.Proof.Pbkdf2.Md.Arm.Fin.inn s₀ ∧ VG.Proof.Pbkdf2.Md.Arm.Fin.blk H s₀' = VG.Proof.Pbkdf2.Md.Arm.Fin.blk H s₀ ∧ VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀' = VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀ ∧ VG.Proof.Pbkdf2.Md.Arm.Fin.hv H s₀' = VG.Proof.Pbkdf2.Md.Arm.Fin.hv H s₀ := by
    refine ⟨hq.r0.symm, ?_, hq.a1.symm, ?_⟩ <;> simp only [VG.Proof.Pbkdf2.Md.Arm.Fin.blk, VG.Proof.Pbkdf2.Md.Arm.Fin.hv, VG.Proof.Pbkdf2.Md.Arm.Fin.scr, hq.a1]
  have hcnt : count s₀ = count s₀' := by rw [count, count, hq.r2, hq.r3]
  have aw : ∀ {t : State}, VG.Proof.Pbkdf2.Md.Arm.Fin.Pre H sc t →
      t.sp.toNat + 8 ≤ 2 ^ 32 ∧ ∀ r ∈ t.wr, Region.Disjoint ⟨State.addr t.sp, 8⟩ r := fun {t} h => by
    have e : (⟨State.addr t.sp, 8⟩ : Region) = VG.Proof.Pbkdf2.Md.Arm.Fin.argR t := by simp [stackArgAddr]
    refine ⟨h.spf, ?_⟩
    simp only [e, h.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact h.a_i
    · exact h.a_p
    · exact h.a_s
  let P₁ : State → State → Prop := fun t₀ s => VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc t₀ s ∧ s.gpr .r0 = VG.Proof.Pbkdf2.Md.Arm.Fin.inn t₀ ∧ count s = count t₀
  let F₁ : State → State → Prop := fun t₀ s =>
    VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc t₀ s ∧ FinArgs hH.stream s (VG.Proof.Pbkdf2.Md.Arm.Fin.inn t₀) (VG.Proof.Pbkdf2.Md.Arm.Fin.blk H t₀) (VG.Proof.Pbkdf2.Md.Arm.Fin.scr t₀) ∧ count s = count t₀
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.finPrologue) fun s s' => P₁ s₀ s ∧ P₁ s₀' s' :=
    rel_agree (argTaint [.r0, .r1, .r2, .r3] 8) (fun s s' e e' => by
        rw [e, e']
        refine agree_argTaint (fun r hr => ?_) hq.sp (aw hp) (aw hp')
          (argMem_of (j := 2) hq.sp hp.spf fun i hi => by
            rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
            · exact hq.a0
            · exact hq.a1)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.r0
        · exact hq.r1
        · exact hq.r2
        · exact hq.r3) hc.pro
      (fun _ e => by rw [e]; exact WP.mono (VG.Proof.Pbkdf2.Md.Arm.Fin.pro_ok hH hp) fun _ ⟨k, r0, c, _⟩ => ⟨k, r0, c⟩)
      (fun _ e => by rw [e]; exact WP.mono (VG.Proof.Pbkdf2.Md.Arm.Fin.pro_ok hH hp') fun _ ⟨k, r0, c, _⟩ => ⟨k, r0, c⟩)
  have f1 := VG.Proof.Pbkdf2.Md.Arm.Fin.rel_regs (F := P₁ s₀) (F' := P₁ s₀') (G := F₁ s₀) (G' := F₁ s₀') VG.Proof.Pbkdf2.Md.Arm.Fin.kregs
    (fun _ _ h h' => VG.Proof.Pbkdf2.Md.Arm.Fin.kr_agree hq h.1 h'.1) hc.fin1
    (fun _ ⟨k, r0, c⟩ => WP.mono (VG.Proof.Pbkdf2.Md.Arm.Fin.fin1Args_ok hH hp k r0) fun _ ⟨k, a, c', _⟩ => ⟨k, a, c'.trans c⟩)
    (fun _ ⟨k, r0, c⟩ => WP.mono (VG.Proof.Pbkdf2.Md.Arm.Fin.fin1Args_ok hH hp' k r0) fun _ ⟨k, a, c', _⟩ => ⟨k, a, c'.trans c⟩)
  have call : RelCT isa (fun s s' => F₁ s₀ s ∧ F₁ s₀' s')
      (.frame (.push Pbkdf2.Stream.Arm.fin2) (.call H.st.finN H.st.finC) (.pop .r1 8))
      fun s s' => VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc s₀ s ∧ VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc s₀' s' :=
    rel_wp (fin_rel hH.stream (sp := s₀.sp) (st := VG.Proof.Pbkdf2.Md.Arm.Fin.inn s₀) (o := VG.Proof.Pbkdf2.Md.Arm.Fin.blk H s₀) (sc := VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀) fun s s' ⟨h, h'⟩ =>
      ⟨h.2.1, by rw [← e.1, ← e.2.1, ← e.2.2.1]; exact h'.2.1, by rw [h.2.2, h'.2.2, hcnt], h.1.sp,
        by rw [h'.1.sp, hq.sp]⟩)
      (fun _ h => VG.Proof.Pbkdf2.Md.Arm.Fin.finCall_ok hH hp h.1 h.2.1 fun _ k _ _ => k)
      (fun _ h => VG.Proof.Pbkdf2.Md.Arm.Fin.finCall_ok hH hp' h.1 h.2.1 fun _ k _ _ => k)
  have mid := VG.Proof.Pbkdf2.Md.Arm.Fin.rel_regs (F := VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc s₀) (F' := VG.Proof.Pbkdf2.Md.Arm.Fin.KR H sc s₀') (G := VG.Proof.Pbkdf2.Md.Arm.Fin.KR' H sc s₀) (G' := VG.Proof.Pbkdf2.Md.Arm.Fin.KR' H sc s₀') VG.Proof.Pbkdf2.Md.Arm.Fin.kregs
    (fun _ _ h h' => VG.Proof.Pbkdf2.Md.Arm.Fin.kr_agree hq h h') hc.mid
    (fun _ h => WP.mono (VG.Proof.Pbkdf2.Md.Arm.Fin.mid_ok hz hp hH.reloc hH.len h) fun _ h => h.1)
    (fun _ h => WP.mono (VG.Proof.Pbkdf2.Md.Arm.Fin.mid_ok hz hp' hH.reloc hH.len h) fun _ h => h.1)
  have cmp : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.Arm.Fin.KR' H sc s₀ s ∧ VG.Proof.Pbkdf2.Md.Arm.Fin.KR' H sc s₀' s') H.compressBlock
      fun s s' => VG.Proof.Pbkdf2.Md.Arm.Fin.KR' H sc s₀ s ∧ VG.Proof.Pbkdf2.Md.Arm.Fin.KR' H sc s₀' s' :=
    rel_wp (VG.Proof.Pbkdf2.Md.Arm.compressBlock_rel (H := hH.md) (so := H.so) hH.comp (name := H.compN) (st := VG.Proof.Pbkdf2.Md.Arm.Fin.hv H s₀) (scr := VG.Proof.Pbkdf2.Md.Arm.Fin.scr s₀)
      (src := VG.Proof.Pbkdf2.Md.Arm.Fin.blk H s₀) fun s s' ⟨h, h'⟩ => by
        have c' := VG.Proof.Pbkdf2.Md.Arm.Fin.callOk_of hz hp' h'
        rw [e.2.2.2, e.2.2.1, e.2.1] at c'
        exact ⟨VG.Proof.Pbkdf2.Md.Arm.Fin.callOk_of hz hp h, c'⟩)
      (fun _ h => VG.Proof.Pbkdf2.Md.Arm.Fin.cmp_ok hz hp hH.comp h fun _ k _ _ => k)
      (fun _ h => VG.Proof.Pbkdf2.Md.Arm.Fin.cmp_ok hz hp' hH.comp h fun _ k _ _ => k)
  obtain ⟨_, ho⟩ := hc.out
  have out : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.Arm.Fin.KR' H sc s₀ s ∧ VG.Proof.Pbkdf2.Md.Arm.Fin.KR' H sc s₀' s') (.block H.finOut) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Pbkdf2.Md.Arm.Fin.regsO) (fun _ _ h => Taint.agree_ofRegs (VG.Proof.Pbkdf2.Md.Arm.Fin.kr'_agree hq h.1 h.2)) ho
  unfold Hash.hmacFin Impl.Pbkdf2.Stream.Arm.Hash.callFin
  exact pro.seq ((f1.seq call).seq (mid.seq (cmp.seq out)))

/-! ## Verified -/

theorem pubEq_of {S : Spec.Hmac.StreamingHash} {W : Nat} {s₁ s₂ : State} (h : (finG S W).pub s₁ s₂) :
    VG.Proof.Pbkdf2.Md.Arm.Fin.PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- HMAC's `finalize` is verified against `finG`, for any hash function the
proof supports (`HashOK`), whose pieces of code the taint analysis accepts
(`Checks`). -/
theorem verified {H : Hash} (hH : VG.Proof.Pbkdf2.Md.Arm.HashOK H) (hc : VG.Proof.Pbkdf2.Md.Arm.Fin.Checks H) {sc : Nat} (hfit : H.st.buf + H.N + H.B ≤ 8 * sc)
    (hsat : ∃ s, (finG hH.SH sc).pre s) :
    Verified Arm.target H.hmacFin (finG hH.SH sc) := by
  refine ⟨fun s hs => VG.Proof.Pbkdf2.Md.Arm.Fin.correct hH (VG.Proof.Pbkdf2.Md.Arm.Fin.pre_of hH hs hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  exact (VG.Proof.Pbkdf2.Md.Arm.Fin.fin_ct hH hc (VG.Proof.Pbkdf2.Md.Arm.Fin.pre_of hH h₁ hfit) (VG.Proof.Pbkdf2.Md.Arm.Fin.pre_of hH h₂ hfit) (VG.Proof.Pbkdf2.Md.Arm.Fin.pubEq_of hpub) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.Arm.Fin

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.Arm.HmacInit`. -/
section

/-!
# HMAC's `init` over a Merkle–Damgård hash function on ARMv7: correct

As on x86 (`Proof/Pbkdf2/Md/X86/HmacInit.lean`): HMAC's `init`
(`Impl/Pbkdf2/Md/Arm.lean`) saves our caller's registers (`pro_ok`), calls
the streaming `init` on both states (`callInit_ok`), writes `ipad` in every
byte of the inner state's buffer (`fill_ok`) and the key XORed into its
start (`keys_ok`), the outer buffer from the inner one, word by word
(`opad_ok`), and compresses each buffer into its state's hash value
(`compressBlock_ok`): each state then represents its block
(`Md.repr_block`). The contract is `initG`
(`Proof/Pbkdf2/Stream/Arm/Hash.lean`), the shared one's at 16 bytes of stack.
-/

namespace VG.Proof.Pbkdf2.Md.Arm

open VG VG.Arm
open VG.Impl.Pbkdf2.Md.Arm (Hash)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_ldr wp_str wp_ldrb wp_strb wp_subs wp_cmp op2_imm
  op2_reg eval_eq)
open VG.Proof.Pbkdf2.Stream.Arm (count_loop addr3 left_z left_val)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open VG.Spec.Sha256 (bytesAt)

/-! ## Words of a constant, and words XORed with a constant -/

/-- `n` words of `r1` stored at `[r4 + o]`, `[r4 + o + 4]`, … -/
theorem fillW_ok {y : BitVec 32} {o : Nat} {b : Byte} (n : Nat) (ho : o + 4 * n ≤ 4096) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .r1 = b ++ b ++ b ++ b →
    s.gpr .r4 = y → y.toNat + o + 4 * n ≤ 2 ^ 32 →
    (∀ k < n, InRegions s.wr (State.addr y + BitVec.ofNat 64 (o + 4 * k)) 4) →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr y + BitVec.ofNat 64 o) (List.replicate (4 * n) b) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).map (fun k => Instr.str .r1 .r4 (o + 4 * k)) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s rfl rfl rfl rfl (by simp [VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro rest s Q hc hy fy hout k
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    refine ih (by omega) _ s Q hc hy (by omega_using [fy]) (fun j hj => hout j (by omega)) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_str (a := State.addr y + BitVec.ofNat 64 (o + 4 * n)) (by omega)
      (by rw [g₁, hy, addr_add (by omega)]) (by rw [wr₁]; exact hout n (by omega)) fun s₂ u₂ => ?_
    refine k s₂ (by rw [u₂.gpr, g₁]) (by rw [u₂.rd, rd₁]) (by rw [u₂.wr, wr₁]) (by rw [u₂.sp, sp₁]) ?_
    rw [u₂.mem, m₁, g₁, hc, MdKeys.writeW_rep, ← Memory.add_ofNat,
      Memory.writeBytes_append' _ _ _ (by rw [List.length_replicate]) (by simp; omega),
      List.replicate_append_replicate, show 4 * n + 4 = 4 * (n + 1) by omega]

/-- The outer state's buffer, from the inner one's: `n` words of
`[r4 + N + 4 k]`, XORed with `r1 = 0x6a6a6a6a`, into `[r5 + N + 4 k]`. -/
theorem opadW_ok (H : Hash) {x y : BitVec 32} (n : Nat) (ho : H.N + 4 * n ≤ 4096) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .r1 = 0x6a6a6a6a → s.gpr .r4 = x →
    s.gpr .r5 = y → x.toNat + H.N + 4 * n ≤ 2 ^ 32 → y.toNat + H.N + 4 * n ≤ 2 ^ 32 →
    (∀ k < n, InRegions (s.rd ++ s.wr) (State.addr x + BitVec.ofNat 64 (H.N + 4 * k)) 4) →
    (∀ k < n, InRegions s.wr (State.addr y + BitVec.ofNat 64 (H.N + 4 * k)) 4) →
    Region.Disjoint ⟨State.addr x + BitVec.ofNat 64 H.N, 4 * n⟩ ⟨State.addr y + BitVec.ofNat 64 H.N, 4 * n⟩ →
    (∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr y + BitVec.ofNat 64 H.N)
        ((bytesAt s.mem (State.addr x + BitVec.ofNat 64 H.N) (4 * n)).map (· ^^^ 0x6a)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap H.opadW ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl rfl (by simp [bytesAt, VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro rest s Q h1 hx hy fx fy hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q h1 hx hy (by omega) (by omega) (fun j hj => hin j (by omega))
      (fun j hj => hout j (by omega))
      ((hsep.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by omega)))
      fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [Hash.opadW, List.cons_append, List.nil_append]
    refine wp_ldr (a := State.addr x + BitVec.ofNat 64 (H.N + 4 * n)) (by omega)
      (by rw [g₁ _ (by decide), hx, addr_add (by omega)]) (by rw [rd₁, wr₁]; exact hin n (by omega))
      fun s₂ u₂ => VG.Proof.Pbkdf2.Md.Arm.wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
    refine wp_str (a := State.addr y + BitVec.ofNat 64 (H.N + 4 * n)) (by omega)
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), hy, addr_add (by omega)])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hout n (by omega)) fun s₄ u₄ => ?_
    refine k s₄ (fun r hr => by rw [u₄.gpr, u₃.other r hr, u₂.other r hr, g₁ r hr])
      (by rw [u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]) (by rw [u₄.sp, u₃.sp, u₂.sp, sp₁]) ?_
    have hl : ((bytesAt s.mem (State.addr x + BitVec.ofNat 64 H.N) (4 * n)).map (· ^^^ (0x6a : Byte))).length =
        4 * n := by simp [bytesAt_length]
    have f₁ : Frame [⟨State.addr y + BitVec.ofNat 64 H.N, 4 * n⟩] s.mem s₁.mem := by
      rw [m₁]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
    have dX : ∀ r ∈ [(⟨State.addr y + BitVec.ofNat 64 H.N, 4 * n⟩ : Region)],
        Region.Disjoint ⟨State.addr x + BitVec.ofNat 64 H.N + BitVec.ofNat 64 (4 * n), 4⟩ r := by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hsep.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by omega))
    have v : s₃.gpr .r12 = s₁.mem.readW (State.addr x + BitVec.ofNat 64 (H.N + 4 * n)) 32 ^^^ 0x6a6a6a6a := by
      rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), g₁ _ (by decide), h1]
    rw [u₄.mem, v, u₃.mem, u₂.mem, ← Memory.add_ofNat, ← Memory.add_ofNat,
      f₁.readW (r := ⟨_, 4⟩) (Region.contains_self _ _) dX (by decide), MdKeys.c6a, MdKeys.writeW_xorRep, m₁,
      Memory.writeBytes_append' _ _ _ (by rw [hl]) (by simp [bytesAt_length]; omega), ← List.map_append,
      ← bytesAt_add, show 4 * n + 4 = 4 * (n + 1) by omega]

/-! ## The key loop -/

/-- After `j` bytes of the key loop, from `s`: the key at `kp`, its bytes,
XORed with `ipad`, written at `p + N`. -/
structure KeyInv (s : State) (kp p : BitVec 32) (N kl j : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r, r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r12 → t.gpr r = s.gpr r
  r6 : t.gpr .r6 = kp + BitVec.ofNat 32 j
  r8 : t.gpr .r8 = p + BitVec.ofNat 32 j
  r7 : t.gpr .r7 = BitVec.ofNat 32 (kl - j)
  mem : t.mem = VG.WriteBytes.writeBytes s.mem (State.addr p + BitVec.ofNat 64 N)
    ((bytesAt s.mem (State.addr kp) j).map (· ^^^ Spec.Hmac.ipad))

theorem key_step (H : Hash) {s : State} {kp p : BitVec 32} {kl : Nat} (hkp : kp.toNat + kl ≤ 2 ^ 32)
    (hp : p.toNat + H.N + kl ≤ 2 ^ 32) (hkl : kl < 2 ^ 32) (hN : H.N < 4096)
    (hin : ∀ j < kl, InRegions (s.rd ++ s.wr) (State.addr kp + BitVec.ofNat 64 j) 1)
    (hout : ∀ j < kl, InRegions s.wr (State.addr p + BitVec.ofNat 64 H.N + BitVec.ofNat 64 j) 1)
    (hsep : Region.Disjoint ⟨State.addr kp, kl⟩ ⟨State.addr p + BitVec.ofNat 64 H.N, kl⟩) {j : Nat} (hj : j < kl)
    {t : State} (h : VG.Proof.Pbkdf2.Md.Arm.KeyInv s kp p H.N kl j t) :
    WP isa (.block [.ldrb .r12 .r6 0, .dp .eor .r12 .r12 (.imm 0x36), .strb .r12 .r8 H.N,
      .dp .add .r6 .r6 (.imm 1), .dp .add .r8 .r8 (.imm 1), .subs .r7 .r7 (.imm 1)]) t
      fun t' => VG.Proof.Pbkdf2.Md.Arm.KeyInv s kp p H.N kl (j + 1) t' ∧ t'.z = decide (kl - (j + 1) = 0) := by
  have hl : ((bytesAt s.mem (State.addr kp) j).map (· ^^^ Spec.Hmac.ipad)).length = j := by
    simp [bytesAt_length]
  have hbyte : t.mem (State.addr kp + BitVec.ofNat 64 j) = s.mem (State.addr kp + BitVec.ofNat 64 j) := by
    rw [h.mem]
    refine (VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)).bytes
      (R := ⟨State.addr kp, kl⟩) (by
        simp only [List.mem_singleton]; rintro r rfl
        exact hsep.sub_right (Region.sub_prefix (by omega))) (by show kl ≤ 2 ^ 64; omega) hj
  refine wp_ldrb (a := State.addr kp + BitVec.ofNat 64 j) (by decide)
    (by rw [h.r6, addr3 (by omega_using [hj, hkp]), BitVec.add_zero]) (by rw [h.rd, h.wr]; exact hin j hj)
    fun t₁ u₁ => VG.Proof.Pbkdf2.Md.Arm.wp_eor (op2_imm (by decide)) fun t₂ u₂ => ?_
  refine wp_strb (a := State.addr p + BitVec.ofNat 64 H.N + BitVec.ofNat 64 j) hN
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r8, addr3 (by omega_using [hj, hp])])
    (by rw [u₂.wr, u₁.wr, h.wr]; exact hout j hj) fun t₃ u₃ => ?_
  refine wp_add (op2_imm (by decide)) fun t₄ u₄ => wp_add (op2_imm (by decide)) fun t₅ u₅ =>
    wp_subs (op2_imm (by decide)) fun t₆ u₆ z₆ => WP.block_nil ?_
  have r7₅ : t₅.gpr .r7 = BitVec.ofNat 32 (kl - j) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
      h.r7]
  have v : (t₂.gpr .r12).setWidth 8 = s.mem (State.addr kp + BitVec.ofNat 64 j) ^^^ Spec.Hmac.ipad := by
    rw [u₂.gpr, u₁.gpr, MdKeys.xor_byte, hbyte]; rfl
  refine ⟨⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr], by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r h6 h7 h8 h12 => by
      rw [u₆.other r h7, u₅.other r h8, u₄.other r h6, u₃.gpr, u₂.other r h12, u₁.other r h12,
        h.other r h6 h7 h8 h12],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r6, BitVec.add_assoc, Proof.Pbkdf2.Stream.Arm.ofNat_succ32],
    by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r8, BitVec.add_assoc, Proof.Pbkdf2.Stream.Arm.ofNat_succ32],
    by rw [u₆.gpr, r7₅, left_val hj], ?_⟩, ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, v, u₂.mem, u₁.mem, h.mem]
    have e := VG.Proof.Hmac.Generic.Common.writeBytes_snoc s.mem (State.addr p + BitVec.ofNat 64 H.N)
      ((bytesAt s.mem (State.addr kp) j).map (· ^^^ Spec.Hmac.ipad))
      (s.mem (State.addr kp + BitVec.ofNat 64 j) ^^^ Spec.Hmac.ipad) (by rw [hl]; omega_using [hj, hkp])
    rw [hl] at e
    rw [e, VG.Proof.Hmac.Generic.Common.bytesAt_snoc', List.map_append, List.map_singleton]
  · rw [z₆, r7₅, left_z hj hkl]

/-- The key loop, skipped for an empty key: from the flags of `kl = 0`. -/
theorem key_ok (H : Hash) {s : State} {kp p : BitVec 32} {kl : Nat} (hkp : kp.toNat + kl ≤ 2 ^ 32)
    (hp : p.toNat + H.N + kl ≤ 2 ^ 32) (hkl : kl < 2 ^ 32) (hN : H.N < 4096)
    (hin : ∀ j < kl, InRegions (s.rd ++ s.wr) (State.addr kp + BitVec.ofNat 64 j) 1)
    (hout : ∀ j < kl, InRegions s.wr (State.addr p + BitVec.ofNat 64 H.N + BitVec.ofNat 64 j) 1)
    (hsep : Region.Disjoint ⟨State.addr kp, kl⟩ ⟨State.addr p + BitVec.ofNat 64 H.N, kl⟩)
    (h0 : VG.Proof.Pbkdf2.Md.Arm.KeyInv s kp p H.N kl 0 s) (hz : s.z = decide (kl = 0)) :
    WP isa (.ite .eq (.block []) H.keyLoop) s (VG.Proof.Pbkdf2.Md.Arm.KeyInv s kp p H.N kl kl) := by
  refine WP.ite (decide (kl = 0)) (by show VG.Arm.eval .eq s = _; rw [eval_eq, hz]) (fun e => WP.block_nil ?_)
    fun e => ?_
  · have : kl = 0 := by simpa using e
    subst this; exact h0
  · exact count_loop (by simp at e; omega) _ (fun j hj t h => VG.Proof.Pbkdf2.Md.Arm.key_step H hkp hp hkl hN hin hout hsep hj h) h0

end VG.Proof.Pbkdf2.Md.Arm

namespace VG.Proof.Pbkdf2.Md.Arm.HmacInit

open VG VG.Arm
open VG.Impl.Pbkdf2.Md.Arm (Hash)
open VG.Proof.Pbkdf2.Md.Arm
open VG.Proof.MdStream (Md)
open VG.Proof.Pbkdf2.Stream.Arm (initG below SavedRegs saveR savedRegs preserved_saved After below_eq covers_one
  init_call save_ok restore_ok)
open VG.Proof.MdStream.Arm (Upd Fupd wp_mov wp_add wp_cmp wp_ldrSp op2_imm op2_reg cmp0)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.Proof.Hmac.Generic.Common (bytesAt_writeBytes_self')
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open VG.Spec.Sha256 (bytesAt)
open VG.Spec.Hmac (xorPad ipad opad blockKey)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev inn : BitVec 32 := s₀.gpr .r0
abbrev out : BitVec 32 := s₀.gpr .r1
abbrev kp : BitVec 32 := s₀.gpr .r2
abbrev kl : Nat := (s₀.gpr .r3).toNat
abbrev scr : BitVec 32 := stackArg s₀ 0
abbrev keyR : Region := ⟨State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp s₀), VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩

end

section
variable (H : Hash) (sc : Nat) (s₀ : State)

abbrev inR : Region := ⟨State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀), H.N + H.B⟩
abbrev outR : Region := ⟨State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀), H.N + H.B⟩
abbrev scR : Region := ⟨State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀), 8 * sc⟩
/-- The compression function's scratch space. -/
abbrev cmpR : Region := ⟨State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀), H.so⟩

end

structure Pre (H : Hash) (sc : Nat) (s₀ : State) : Prop where
  kl_le : VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀ ≤ H.B
  rd : s₀.rd = [VG.Proof.Pbkdf2.Md.Arm.HmacInit.keyR s₀, VG.Proof.Pbkdf2.Md.Arm.HmacInit.argR s₀]
  wr : s₀.wr = [VG.Proof.Pbkdf2.Md.Arm.HmacInit.inR H s₀, VG.Proof.Pbkdf2.Md.Arm.HmacInit.outR H s₀, VG.Proof.Pbkdf2.Md.Arm.HmacInit.scR sc s₀]
  i_o : (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.HmacInit.outR H s₀)
  i_s : (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.HmacInit.scR sc s₀)
  o_s : (VG.Proof.Pbkdf2.Md.Arm.HmacInit.outR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.HmacInit.scR sc s₀)
  k_i : (VG.Proof.Pbkdf2.Md.Arm.HmacInit.keyR s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inR H s₀)
  k_o : (VG.Proof.Pbkdf2.Md.Arm.HmacInit.keyR s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.HmacInit.outR H s₀)
  k_s : (VG.Proof.Pbkdf2.Md.Arm.HmacInit.keyR s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.HmacInit.scR sc s₀)
  a_i : (VG.Proof.Pbkdf2.Md.Arm.HmacInit.argR s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inR H s₀)
  a_o : (VG.Proof.Pbkdf2.Md.Arm.HmacInit.argR s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.HmacInit.outR H s₀)
  a_s : (VG.Proof.Pbkdf2.Md.Arm.HmacInit.argR s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.HmacInit.scR sc s₀)
  b_i : (below s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inR H s₀)
  b_o : (below s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.HmacInit.outR H s₀)
  b_k : (below s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.HmacInit.keyR s₀)
  b_s : (below s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.HmacInit.scR sc s₀)
  ni : (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀).toNat + (H.N + H.B) ≤ 2 ^ 32
  no : (VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀).toNat + (H.N + H.B) ≤ 2 ^ 32
  nk : (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp s₀).toNat + VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀ ≤ 2 ^ 32
  nw : (VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  sp16 : 16 ≤ s₀.sp.toNat
  spf : s₀.sp.toNat + 4 ≤ 2 ^ 32
  fits : H.st.buf ≤ 8 * sc

theorem pre_of {H : Hash} (hH : VG.Proof.Pbkdf2.Md.Arm.HashOK H) {sc : Nat} {s₀ : State} (h : (initG hH.SH sc).pre s₀)
    (hfit : H.st.buf ≤ 8 * sc) : VG.Proof.Pbkdf2.Md.Arm.HmacInit.Pre H sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩ := h
  have hS : hH.SH.stateBytes = H.N + H.B := hH.hS
  have hB := hH.hB
  simp only [hS, hB] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, hfit⟩

/-! ## Sizes and regions -/

section
variable {H : Hash} (hz : VG.Proof.Pbkdf2.Md.Arm.Sizes H) {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.Arm.HmacInit.Pre H sc s₀)
include hz hp

theorem bounds : H.st.buf = 8 * H.st.W + 36 ∧ 8 * H.st.W + 36 ≤ 8 * sc ∧ (VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀).toNat + 8 * sc ≤ 2 ^ 32 ∧
    H.so ≤ 8 * H.st.W ∧ H.st.W ≤ 64 ∧ H.N ≤ 64 ∧ H.N % 4 = 0 ∧ H.B % 4 = 0 ∧ 64 ≤ H.B ∧ H.B ≤ 128 ∧
    (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀).toNat + (H.N + H.B) ≤ 2 ^ 32 ∧ (VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀).toNat + (H.N + H.B) ≤ 2 ^ 32 ∧
    (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp s₀).toNat + VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀ ≤ 2 ^ 32 ∧ VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀ ≤ H.B := by
  have hB : H.B % 4 = 0 ∧ 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> rw [h] <;> decide
  exact ⟨rfl, hp.fits, hp.nw, hz.so, hz.W, hz.N64, hz.N4, hB.1, hB.2.1, hB.2.2, hp.ni, hp.no, hp.nk, hp.kl_le⟩

theorem save_sub : Region.Sub (saveR H.st (VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀)) (VG.Proof.Pbkdf2.Md.Arm.HmacInit.scR sc s₀) := by
  have := VG.Proof.Pbkdf2.Md.Arm.HmacInit.bounds hz hp; exact Offset.sub_base _ (by omega)

theorem cmp_sub : Region.Sub (VG.Proof.Pbkdf2.Md.Arm.HmacInit.cmpR H s₀) (VG.Proof.Pbkdf2.Md.Arm.HmacInit.scR sc s₀) := by
  have := VG.Proof.Pbkdf2.Md.Arm.HmacInit.bounds hz hp; exact Region.sub_prefix (by omega)

theorem save_cmp : (saveR H.st (VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀)).Disjoint (VG.Proof.Pbkdf2.Md.Arm.HmacInit.cmpR H s₀) := by
  have := VG.Proof.Pbkdf2.Md.Arm.HmacInit.bounds hz hp
  exact Offset.disjoint_base _ (by omega) (by omega)

omit hz hp in
/-- A part of a state at `p`. -/
theorem st_sub (p : BitVec 32) {a n : Nat} (h : a + n ≤ H.N + H.B) :
    Region.Sub ⟨State.addr p + BitVec.ofNat 64 a, n⟩ ⟨State.addr p, H.N + H.B⟩ := Offset.sub_base _ h

/-- The states, `scratch` and the stack below the stack pointer, as the code sees them. -/
theorem st_facts {p : BitVec 32} (hpR : p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀ ∨ p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀) :
    Region.Disjoint ⟨State.addr p, H.N + H.B⟩ (VG.Proof.Pbkdf2.Md.Arm.HmacInit.scR sc s₀) ∧ (below s₀).Disjoint ⟨State.addr p, H.N + H.B⟩ ∧
      (saveR H.st (VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀)).Disjoint ⟨State.addr p, H.N + H.B⟩ ∧ p.toNat + (H.N + H.B) ≤ 2 ^ 32 ∧
      ⟨State.addr p, H.N + H.B⟩ ∈ s₀.wr := by
  rcases hpR with rfl | rfl
  · exact ⟨hp.i_s, hp.b_i, hp.i_s.symm.sub_left (VG.Proof.Pbkdf2.Md.Arm.HmacInit.save_sub hz hp), hp.ni, by rw [hp.wr]; simp⟩
  · exact ⟨hp.o_s, hp.b_o, hp.o_s.symm.sub_left (VG.Proof.Pbkdf2.Md.Arm.HmacInit.save_sub hz hp), hp.no, by rw [hp.wr]; simp⟩

end

/-! ## What the pieces keep -/

/-- The regions everything writes: our buffers and the stack below the stack pointer. -/
abbrev wrs (H : Hash) (sc : Nat) (s₀ : State) : List Region := [VG.Proof.Pbkdf2.Md.Arm.HmacInit.inR H s₀, VG.Proof.Pbkdf2.Md.Arm.HmacInit.outR H s₀, VG.Proof.Pbkdf2.Md.Arm.HmacInit.scR sc s₀, below s₀]

/-- The registers and memory kept from the prologue on. -/
structure KR (H : Hash) (sc : Nat) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀
  r5 : s.gpr .r5 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀
  r11 : s.gpr .r11 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀
  saved : SavedRegs H.st (VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀) s₀ s.mem
  frame : Frame (VG.Proof.Pbkdf2.Md.Arm.HmacInit.wrs H sc s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.r4, .r5, .r11]

theorem kregs_pres : ∀ r ∈ VG.Proof.Pbkdf2.Md.Arm.HmacInit.kregs, r ∈ preserved ∧ r ≠ .lr := by decide

section
variable {H : Hash} {sc : Nat} {s₀ : State}

theorem KR.keep {s s' : State} (h : VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ VG.Proof.Pbkdf2.Md.Arm.HmacInit.kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H.st (VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀)).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ VG.Proof.Pbkdf2.Md.Arm.HmacInit.wrs H sc s₀, Region.Sub r r') : VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.r4,
    (hg _ (by simp)).trans h.r5, (hg _ (by simp)).trans h.r11, h.saved.frame H.st hf hs,
    h.frame.trans (hf.sub hsub)⟩

theorem KR.upd {s s' : State} (h : VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s) {d : Reg} (hd : d ∉ VG.Proof.Pbkdf2.Md.Arm.HmacInit.kregs) {v : BitVec 32}
    (u : Upd s s' d v) : VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s' :=
  h.keep u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp) (by simp)

/-- The key, while `KR` holds. -/
theorem KR.key {s : State} (hp : VG.Proof.Pbkdf2.Md.Arm.HmacInit.Pre H sc s₀) (hk : VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s) :
    bytesAt s.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp s₀)) (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀) = bytesAt s₀.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp s₀)) (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀) :=
  Memory.frame_bytesAt hk.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.k_i
    · exact hp.k_o
    · exact hp.k_s
    · exact hp.b_k.symm) (Nat.le_of_lt (Nat.lt_trans (s₀.gpr .r3).isLt (by decide)))

end

/-! ## The pieces -/

/-- The offsets of the buffers in a state can be added as immediates. -/
theorem enc_small : ∀ n < 65, encodable (BitVec.ofNat 32 n) = true := by decide

section
variable {H : Hash} (hz : VG.Proof.Pbkdf2.Md.Arm.Sizes H) {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.Arm.HmacInit.Pre H sc s₀)
include hz hp

theorem pro_ok : WP isa (.block H.initPrologue) s₀ fun s => VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s ∧ s.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp s₀ ∧
    s.gpr .r7 = BitVec.ofNat 32 (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀) := by
  obtain ⟨hb, hf, nw, -, hW, -⟩ := VG.Proof.Pbkdf2.Md.Arm.HmacInit.bounds hz hp
  have hsc : VG.Proof.Pbkdf2.Md.Arm.HmacInit.scR sc s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  unfold Hash.initPrologue
  simp only [List.singleton_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl
    (by rw [hp.rd]; exact ⟨VG.Proof.Pbkdf2.Md.Arm.HmacInit.argR s₀, by simp, Region.contains_self _ _⟩) fun s₁ u₁ => ?_
  refine VG.Proof.Pbkdf2.Stream.Arm.save_ok H.st (scr := VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀) u₁.gpr hW (by rw [u₁.wr]; exact hsc) (L := 8 * sc) (by omega) nw
    fun s₂ g₂ rd₂ wr₂ sp₂ f₂ sv₂ => ?_
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  have e₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  have hm : s₇.mem = s₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have f₂' : Frame [saveR H.st (VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀)] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  refine ⟨⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd], by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp],
    by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      e₂ _ (by decide)],
    by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      e₂ _ (by decide)],
    by rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      g₂, u₁.gpr]; rfl,
    hm ▸ sv₂.of_eq H.st fun r hr => u₁.other r (by
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    hm ▸ f₂'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Pbkdf2.Md.Arm.HmacInit.scR sc s₀, by simp, VG.Proof.Pbkdf2.Md.Arm.HmacInit.save_sub hz hp⟩⟩,
    by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide)],
    by rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩

/-- A call of the streaming `init` on the state at `p`, in `r0`. -/
theorem initCall_ok (hH : VG.Proof.Pbkdf2.Md.Arm.HashOK H) {t : State} (hk : VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ t) {p : BitVec 32}
    (hpR : p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀ ∨ p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀) (h0 : t.gpr .r0 = p) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s' → (∀ r ∈ [Reg.r6, .r7], s'.gpr r = t.gpr r) →
      Frame [⟨State.addr p, H.N + H.B⟩, below s₀] t.mem s'.mem → hH.SH.Repr s'.mem (State.addr p) [] → Q s') :
    WP isa (.call H.st.initN H.st.initC) t Q := by
  obtain ⟨_, _, dV, np, hin⟩ := VG.Proof.Pbkdf2.Md.Arm.HmacInit.st_facts hz hp hpR
  have hS : H.st.S = H.N + H.B := hz.S
  refine init_call hH.stream (st := p) h0 (by rw [hS]; exact np) (by rw [hk.wr, hS]; exact covers_one hin)
    fun s' ha hr => ?_
  rw [hS] at ha
  have f := ha.frame
  rw [below_eq hk.sp] at f
  have f' : Frame [⟨State.addr p, H.N + H.B⟩, below s₀] t.mem s'.mem := f
  refine hQ s' (hk.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kregs_pres r hr).1 (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kregs_pres r hr).2) f' ?_ ?_)
    (fun r hr => ?_) f' hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact dV
    · exact hp.b_s.symm.sub_left (VG.Proof.Pbkdf2.Md.Arm.HmacInit.save_sub hz hp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · rcases hpR with rfl | rfl
      · exact ⟨VG.Proof.Pbkdf2.Md.Arm.HmacInit.inR H s₀, by simp, fun _ h => h⟩
      · exact ⟨VG.Proof.Pbkdf2.Md.Arm.HmacInit.outR H s₀, by simp, fun _ h => h⟩
    · exact ⟨below s₀, by simp, fun _ h => h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ha.cs .r6 (by decide) (by decide)
    · exact ha.cs .r7 (by decide) (by decide)

omit hz hp in
/-- `r0` at the state in `st`. -/
theorem initArg_ok {s : State} (hk : VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s) {st : Reg} {p : BitVec 32}
    (hst : st = .r4 ∧ p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀ ∨ st = .r5 ∧ p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀) :
    WP isa (.block [.mov .r0 (.reg st)]) s fun t => VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ t ∧ t.gpr .r0 = p ∧
      (∀ r ∈ [Reg.r6, .r7], t.gpr r = s.gpr r) ∧ t.mem = s.mem :=
  wp_mov (op2_reg _ _) fun _ u₁ => WP.block_nil ⟨hk.upd (by rcases hst with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide) u₁,
    by rw [u₁.gpr]; rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [hk.r4, hk.r5],
    fun r hr => u₁.other r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                               rcases hr with rfl | rfl <;> decide), u₁.mem⟩

/-- A call of the streaming `init` on the state at `p`, in `st`. -/
theorem callInit_ok (hH : VG.Proof.Pbkdf2.Md.Arm.HashOK H) {s : State} (hk : VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s) {st : Reg} {p : BitVec 32}
    (hst : st = .r4 ∧ p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀ ∨ st = .r5 ∧ p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s' → (∀ r ∈ [Reg.r6, .r7], s'.gpr r = s.gpr r) →
      Frame [⟨State.addr p, H.N + H.B⟩, below s₀] s.mem s'.mem → hH.SH.Repr s'.mem (State.addr p) [] → Q s') :
    WP isa (H.st.callInit st) s Q := by
  have hpR : p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀ ∨ p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀ := by rcases hst with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  unfold Impl.Pbkdf2.Stream.Arm.Hash.callInit
  exact WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.Arm.HmacInit.initArg_ok hk hst) fun t ⟨k, d, g, m⟩ =>
    VG.Proof.Pbkdf2.Md.Arm.HmacInit.initCall_ok hz hp hH k hpR d fun s' k' g' f r => hQ s' k' (fun r hr => (g' r hr).trans (g r hr)) (m ▸ f) r)

/-- A word of the buffer of the state at `p`. -/
theorem buf_word {p : BitVec 32} (hpR : p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀ ∨ p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀) {k : Nat} (hk : k < H.B / 4) :
    InRegions s₀.wr (State.addr p + BitVec.ofNat 64 (H.N + 4 * k)) 4 := by
  obtain ⟨-, -, -, -, -, hN, -, hB4, -⟩ := VG.Proof.Pbkdf2.Md.Arm.HmacInit.bounds hz hp
  obtain ⟨-, -, -, np, hin⟩ := VG.Proof.Pbkdf2.Md.Arm.HmacInit.st_facts hz hp hpR
  exact ⟨_, hin, Offset.contains_base _ (by omega) (by omega)⟩

/-- `ipad` in every byte of the inner buffer, and the flags of `key_len = 0`. -/
theorem fill_ok {s : State} (hk : VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s) (h6 : s.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp s₀)
    (h7 : s.gpr .r7 = BitVec.ofNat 32 (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀)) :
    WP isa (.block H.fillIpad) s fun t => VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ t ∧ t.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp s₀ ∧
      t.gpr .r7 = BitVec.ofNat 32 (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀) ∧ t.gpr .r8 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀ ∧ t.z = decide (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀ = 0) ∧
      t.mem = VG.WriteBytes.writeBytes s.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) + BitVec.ofNat 64 H.N) (List.replicate H.B 0x36) := by
  obtain ⟨-, -, -, -, -, hN, -, hB4, hB64, hB, ni, -⟩ := VG.Proof.Pbkdf2.Md.Arm.HmacInit.bounds hz hp
  have h4 : 4 * (H.B / 4) = H.B := by omega
  simp only [Hash.fillIpad, List.cons_append, List.append_assoc]
  refine VG.Proof.Pbkdf2.Md.Arm.wp_movw fun s₁ u₁ => VG.Proof.Pbkdf2.Md.Arm.wp_movt fun s₂ u₂ => ?_
  have c₂ : s₂.gpr .r1 = (0x36 : Byte) ++ (0x36 : Byte) ++ (0x36 : Byte) ++ (0x36 : Byte) := by
    rw [u₂.gpr, u₁.gpr]; decide
  have hr4 : s₂.gpr .r4 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hk.r4]
  refine VG.Proof.Pbkdf2.Md.Arm.fillW_ok (H.B / 4) (by omega) _ s₂ _ c₂ hr4 (by omega)
    (fun j hj => by rw [u₂.wr, u₁.wr, hk.wr]; exact VG.Proof.Pbkdf2.Md.Arm.HmacInit.buf_word hz hp (.inl rfl) hj) fun s₃ g₃ rd₃ wr₃ sp₃ m₃ => ?_
  rw [h4] at m₃
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r1 → r ≠ .r8 → s₅.gpr r = s.gpr r := fun r h1 h8 => by
    rw [f₅.gpr, u₄.other r h8, g₃, u₂.other r h1, u₁.other r h1]
  have sB := VG.Proof.Pbkdf2.Md.Arm.HmacInit.st_sub (H := H) (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) (a := H.N) (n := H.B) (by omega)
  have f : Frame [⟨State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) + BitVec.ofNat 64 H.N, H.B⟩] s.mem s₅.mem := by
    rw [f₅.mem, u₄.mem, m₃, u₂.mem, u₁.mem]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by simp only [List.length_replicate]; exact Region.contains_self _ _)
  refine ⟨hk.keep (by rw [f₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd]) (by rw [f₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr])
      (by rw [f₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp]) (fun r hr => g r (by revert hr; decide +revert)
        (by revert hr; decide +revert)) f
      (by
        simp only [List.mem_singleton]; rintro r rfl
        exact (hp.i_s.symm.sub_left (VG.Proof.Pbkdf2.Md.Arm.HmacInit.save_sub hz hp)).sub_right sB)
      (by simp only [List.mem_singleton]; rintro r rfl; exact ⟨_, by simp, sB⟩),
    by rw [g _ (by decide) (by decide), h6], by rw [g _ (by decide) (by decide), h7],
    by rw [f₅.gpr, u₄.gpr, g₃, hr4], ?_, by rw [f₅.mem, u₄.mem, m₃, u₂.mem, u₁.mem]⟩
  rw [z₅, u₄.other _ (by decide), g₃, u₂.other _ (by decide), u₁.other _ (by decide), h7,
    cmp0 (s₀.gpr .r3).isLt]

/-- The key loop: the key XORed with `ipad` over the start of the inner buffer. -/
theorem keys_ok {s : State} (hk : VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s) (h6 : s.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp s₀) (h7 : s.gpr .r7 = BitVec.ofNat 32 (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀))
    (h8 : s.gpr .r8 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) (hzf : s.z = decide (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀ = 0))
    (hm : bytesAt s.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) + BitVec.ofNat 64 H.N) H.B = List.replicate H.B 0x36) :
    WP isa (.ite .eq (.block []) H.keyLoop) s fun t => VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ t ∧
      Frame [⟨State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) + BitVec.ofNat 64 H.N, H.B⟩] s.mem t.mem ∧
      bytesAt t.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) + BitVec.ofNat 64 H.N) H.B =
        (bytesAt s₀.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp s₀)) (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀)).map (· ^^^ ipad) ++ List.replicate (H.B - VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀) ipad := by
  obtain ⟨-, -, -, -, -, hN, -, -, hB64, hB, ni, -, nk, hkl⟩ := VG.Proof.Pbkdf2.Md.Arm.HmacInit.bounds hz hp
  have kl32 : VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀ < 2 ^ 32 := (s₀.gpr .r3).isLt
  have hin : ∀ j < VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀, InRegions (s.rd ++ s.wr) (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp s₀) + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hk.rd, hp.rd]; exact ⟨VG.Proof.Pbkdf2.Md.Arm.HmacInit.keyR s₀, by simp, Offset.contains_base _ (by omega) (by omega_using [hj, nk])⟩
  have hout : ∀ j < VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀, InRegions s.wr (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) + BitVec.ofNat 64 H.N + BitVec.ofNat 64 j) 1 :=
    fun j hj => by
      rw [hk.wr, hp.wr, Memory.add_ofNat]
      exact ⟨VG.Proof.Pbkdf2.Md.Arm.HmacInit.inR H s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hsep : Region.Disjoint ⟨State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp s₀), VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀⟩ ⟨State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) + BitVec.ofNat 64 H.N, VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀⟩ :=
    hp.k_i.sub_right (VG.Proof.Pbkdf2.Md.Arm.HmacInit.st_sub _ (by omega))
  have h0 : VG.Proof.Pbkdf2.Md.Arm.KeyInv s (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp s₀) (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) H.N (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀) 0 s :=
    ⟨rfl, rfl, rfl, fun _ _ _ _ _ => rfl, by rw [h6]; exact (BitVec.add_zero _).symm,
      by rw [h8]; exact (BitVec.add_zero _).symm, by rw [h7, Nat.sub_zero],
      by rw [show bytesAt s.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp s₀)) 0 = [] from rfl, List.map_nil, VG.WriteBytes.writeBytes_nil]⟩
  refine WP.mono (VG.Proof.Pbkdf2.Md.Arm.key_ok H (by omega) (by omega) kl32 (by omega) hin hout hsep h0 hzf) fun t ht => ?_
  have hl : ((bytesAt s.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp s₀)) (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀)).map (· ^^^ ipad)).length = VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀ := by
    simp [bytesAt_length]
  have sB := VG.Proof.Pbkdf2.Md.Arm.HmacInit.st_sub (H := H) (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) (a := H.N) (n := H.B) (by omega)
  have ft : Frame [⟨State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) + BitVec.ofNat 64 H.N, H.B⟩] s.mem t.mem := by
    rw [ht.mem]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hl]; exact Memory.contains_base hkl)
  refine ⟨hk.keep ht.rd ht.wr ht.sp (fun r hr => ht.other r (by revert hr; decide +revert)
      (by revert hr; decide +revert) (by revert hr; decide +revert) (by revert hr; decide +revert)) ft
      (by
        simp only [List.mem_singleton]; rintro r rfl
        exact (hp.i_s.symm.sub_left (VG.Proof.Pbkdf2.Md.Arm.HmacInit.save_sub hz hp)).sub_right sB)
      (by simp only [List.mem_singleton]; rintro r rfl; exact ⟨_, by simp, sB⟩), ft, ?_⟩
  rw [ht.mem, MdKeys.bytes_over (by rw [hl]; omega) (by omega) hm, hl, hk.key hp]
  rfl

/-- What the compression of the buffer of the state at `p` needs. -/
theorem callOk {s : State} (hk : VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s) {p : BitVec 32} (hpR : p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀ ∨ p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀)
    (h0 : s.gpr .r0 = p) (h3 : s.gpr .r3 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀) (h6 : s.gpr .r6 = p + BitVec.ofNat 32 H.N) :
    VG.Proof.Pbkdf2.Md.Arm.CallOk s H.N H.B H.so p (VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀) (p + BitVec.ofNat 32 H.N) := by
  obtain ⟨hb, hf, nw, hso, hW, hN, -, -, hB64, hB, -⟩ := VG.Proof.Pbkdf2.Md.Arm.HmacInit.bounds hz hp
  obtain ⟨dS, _, _, np, hin⟩ := VG.Proof.Pbkdf2.Md.Arm.HmacInit.st_facts hz hp hpR
  have ap : State.addr (p + BitVec.ofNat 32 H.N) = State.addr p + BitVec.ofNat 64 H.N := addr_add (by omega_using [np, hB64])
  have tp : (p + BitVec.ofNat 32 H.N).toNat = p.toNat + H.N := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := H.N) (by omega), Nat.mod_eq_of_lt (by omega)]
  have sN : Region.Sub ⟨State.addr p, H.N⟩ ⟨State.addr p, H.N + H.B⟩ := Region.sub_prefix (by omega)
  have sB := VG.Proof.Pbkdf2.Md.Arm.HmacInit.st_sub (H := H) p (a := H.N) (n := H.B) (by omega)
  have sS : VG.Proof.Pbkdf2.Md.Arm.HmacInit.scR sc s₀ ∈ s.wr := by rw [hk.wr, hp.wr]; simp
  have hin' : ⟨State.addr p, H.N + H.B⟩ ∈ s.wr := by rw [hk.wr]; exact hin
  refine ⟨h0, h3, h6, by omega_using [np], by rw [tp]; omega_using [np], by omega, dS.sub_left sN |>.sub_right (VG.Proof.Pbkdf2.Md.Arm.HmacInit.cmp_sub hz hp),
    by rw [ap]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hB, hN]),
    by rw [ap]; exact dS.sub_left sB |>.sub_right (VG.Proof.Pbkdf2.Md.Arm.HmacInit.cmp_sub hz hp), ?_, ?_⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [ap]; exact ⟨_, List.mem_append_right _ hin', H.N, rfl, by simp only; omega⟩
    · exact ⟨_, List.mem_append_right _ hin', 0, (BitVec.add_zero _).symm, by simp only; omega⟩
    · exact ⟨_, List.mem_append_right _ sS, 0, (BitVec.add_zero _).symm, by simp only; omega⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hin', 0, (BitVec.add_zero _).symm, by simp only; omega⟩
    · exact ⟨_, sS, 0, (BitVec.add_zero _).symm, by simp only; omega⟩

/-- The outer buffer from the inner one, and the inner state's compression set up. -/
theorem opad_ok {s : State} (hk : VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s) :
    WP isa (.block H.fillOpad) s fun t => VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ t ∧ t.gpr .r0 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀ ∧ t.gpr .r3 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀ ∧
      t.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀ + BitVec.ofNat 32 H.N ∧
      t.mem = VG.WriteBytes.writeBytes s.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀) + BitVec.ofNat 64 H.N)
        ((bytesAt s.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) + BitVec.ofNat 64 H.N) H.B).map (· ^^^ 0x6a)) := by
  obtain ⟨-, -, -, -, -, hN, -, hB4, hB64, hB, ni, no, -⟩ := VG.Proof.Pbkdf2.Md.Arm.HmacInit.bounds hz hp
  have h4 : 4 * (H.B / 4) = H.B := by omega
  have sBI := VG.Proof.Pbkdf2.Md.Arm.HmacInit.st_sub (H := H) (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) (a := H.N) (n := H.B) (by omega)
  have sBO := VG.Proof.Pbkdf2.Md.Arm.HmacInit.st_sub (H := H) (VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀) (a := H.N) (n := H.B) (by omega)
  simp only [Hash.fillOpad, List.cons_append, List.append_assoc]
  refine VG.Proof.Pbkdf2.Md.Arm.wp_movw fun s₁ u₁ => VG.Proof.Pbkdf2.Md.Arm.wp_movt fun s₂ u₂ => ?_
  have c₂ : s₂.gpr .r1 = 0x6a6a6a6a := by rw [u₂.gpr, u₁.gpr]; decide
  refine VG.Proof.Pbkdf2.Md.Arm.opadW_ok H (H.B / 4) (by omega) _ s₂ _ c₂ (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hk.r4])
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hk.r5]) (by omega) (by omega)
    (fun j hj => by rw [u₂.wr, u₂.rd, u₁.wr, u₁.rd, hk.wr, hk.rd]
                    exact Hmac.Generic.Common.InRegions.right' (VG.Proof.Pbkdf2.Md.Arm.HmacInit.buf_word hz hp (.inl rfl) hj))
    (fun j hj => by rw [u₂.wr, u₁.wr, hk.wr]; exact VG.Proof.Pbkdf2.Md.Arm.HmacInit.buf_word hz hp (.inr rfl) hj)
    (by rw [h4]; exact (hp.i_o.sub_left sBI).sub_right sBO) fun s₃ g₃ rd₃ wr₃ sp₃ m₃ => ?_
  rw [h4, u₂.mem, u₁.mem] at m₃
  refine wp_mov (op2_reg _ _) fun s₄ u₄ =>
    wp_add (op2_imm (VG.Proof.Pbkdf2.Md.Arm.HmacInit.enc_small _ (by omega))) fun s₅ u₅ => wp_mov (op2_reg _ _) fun s₆ u₆ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r1 → r ≠ .r12 → s₃.gpr r = s.gpr r := fun r h1 h12 => by
    rw [g₃ r h12, u₂.other r h1, u₁.other r h1]
  have hl : ((bytesAt s.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) + BitVec.ofNat 64 H.N) H.B).map (· ^^^ (0x6a : Byte))).length =
      H.B := by simp [bytesAt_length]
  have f : Frame [⟨State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀) + BitVec.ofNat 64 H.N, H.B⟩] s.mem s₆.mem := by
    rw [u₆.mem, u₅.mem, u₄.mem, m₃]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  refine ⟨hk.keep (by rw [u₆.rd, u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd]) (by rw [u₆.wr, u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr])
      (by rw [u₆.sp, u₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp])
      (fun r hr => by
        rw [u₆.other r (by revert hr; decide +revert), u₅.other r (by revert hr; decide +revert),
          u₄.other r (by revert hr; decide +revert), g r (by revert hr; decide +revert) (by revert hr; decide +revert)])
      f
      (by
        simp only [List.mem_singleton]; rintro r rfl
        exact (hp.o_s.symm.sub_left (VG.Proof.Pbkdf2.Md.Arm.HmacInit.save_sub hz hp)).sub_right sBO)
      (by simp only [List.mem_singleton]; rintro r rfl; exact ⟨_, by simp, sBO⟩),
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g _ (by decide) (by decide), hk.r4],
    by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g _ (by decide) (by decide), hk.r11],
    by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g _ (by decide) (by decide), hk.r4],
    by rw [u₆.mem, u₅.mem, u₄.mem, m₃]⟩

/-- The two blocks, as the constant-time proof needs them. -/
theorem blocks_ok {s : State} (hk : VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s) (h6 : s.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp s₀)
    (h7 : s.gpr .r7 = BitVec.ofNat 32 (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀)) :
    WP isa H.blocks s fun t => VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ t ∧ t.gpr .r0 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀ ∧ t.gpr .r3 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀ ∧
      t.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀ + BitVec.ofNat 32 H.N := by
  have := (VG.Proof.Pbkdf2.Md.Arm.HmacInit.bounds hz hp).2.2.2.2.2.2.2.2.2.1
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.Arm.HmacInit.fill_ok hz hp hk h6 h7) fun s₄ ⟨k₄, d₄, c₄, e₄, z₄, m₄⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.Arm.HmacInit.keys_ok hz hp k₄ d₄ c₄ e₄ z₄ (by
    rw [m₄, bytesAt_writeBytes_self' (List.length_replicate ..) (by omega)])) fun s₅ ⟨k₅, _⟩ => ?_)
  exact WP.mono (VG.Proof.Pbkdf2.Md.Arm.HmacInit.opad_ok hz hp k₅) fun _ ⟨k₆, a, b, c, _⟩ => ⟨k₆, a, b, c⟩

/-- The compression of the buffer of the state at `p`, at `r0`, with its
buffer at `r6` and `scratch` at `r3`. -/
theorem cmpS_ok (hH : VG.Proof.Pbkdf2.Md.Arm.HashOK H) {s : State} (hk : VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s) {p : BitVec 32}
    (hpR : p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀ ∨ p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀) (h0 : s.gpr .r0 = p) (h3 : s.gpr .r3 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀)
    (h6 : s.gpr .r6 = p + BitVec.ofNat 32 H.N) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s' → s'.gpr .r3 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀ →
      Frame [⟨State.addr p, H.N⟩, VG.Proof.Pbkdf2.Md.Arm.HmacInit.cmpR H s₀] s.mem s'.mem →
      hH.md.stateAt s'.mem (State.addr p) = hH.md.compress (hH.md.stateAt s.mem (State.addr p))
        (hH.md.blockAt s.mem (State.addr p + BitVec.ofNat 64 H.N)) → Q s') :
    WP isa H.compressBlock s Q := by
  obtain ⟨hb, hf, nw, hso, hW, hN, -, -, hB64, hB, -⟩ := VG.Proof.Pbkdf2.Md.Arm.HmacInit.bounds hz hp
  obtain ⟨_, _, dV, np, _⟩ := VG.Proof.Pbkdf2.Md.Arm.HmacInit.st_facts hz hp hpR
  have sN : Region.Sub ⟨State.addr p, H.N⟩ ⟨State.addr p, H.N + H.B⟩ := Region.sub_prefix (by omega)
  refine VG.Proof.Pbkdf2.Md.Arm.compressBlock_ok hH.comp (VG.Proof.Pbkdf2.Md.Arm.HmacInit.callOk hz hp hk hpR h0 h3 h6) fun s' hrd hwr hcs h0' h3' hsp hfr hst => ?_
  rw [addr_add (by omega)] at hst
  refine hQ s' (hk.keep hrd hwr hsp (fun r hr => hcs r (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kregs_pres r hr).1 (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kregs_pres r hr).2) hfr ?_ ?_) h3' hfr hst
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact dV.sub_right sN
    · exact VG.Proof.Pbkdf2.Md.Arm.HmacInit.save_cmp hz hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · rcases hpR with rfl | rfl
      · exact ⟨VG.Proof.Pbkdf2.Md.Arm.HmacInit.inR H s₀, by simp, sN⟩
      · exact ⟨VG.Proof.Pbkdf2.Md.Arm.HmacInit.outR H s₀, by simp, sN⟩
    · exact ⟨VG.Proof.Pbkdf2.Md.Arm.HmacInit.scR sc s₀, by simp, VG.Proof.Pbkdf2.Md.Arm.HmacInit.cmp_sub hz hp⟩

omit hp in
/-- The outer state's compression set up. -/
theorem toOuter_ok {s : State} (hk : VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s) (h3 : s.gpr .r3 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀) :
    WP isa (.block H.toOuter) s fun t => VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ t ∧ t.gpr .r0 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀ ∧ t.gpr .r3 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀ ∧
      t.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀ + BitVec.ofNat 32 H.N ∧ t.mem = s.mem := by
  have hz_N64 := hz.N64
  unfold Hash.toOuter
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_add (op2_imm (VG.Proof.Pbkdf2.Md.Arm.HmacInit.enc_small _ (by omega))) fun s₂ u₂ => WP.block_nil ?_
  exact ⟨(hk.upd (by decide) u₁).upd (by decide) u₂, by rw [u₂.other _ (by decide), u₁.gpr, hk.r5],
    by rw [u₂.other _ (by decide), u₁.other _ (by decide), h3], by rw [u₂.gpr, u₁.other _ (by decide), hk.r5],
    by rw [u₂.mem, u₁.mem]⟩

end

/-! ## Correctness -/

section
variable {H : Hash} {sc : Nat} {s₀ : State} (hH : VG.Proof.Pbkdf2.Md.Arm.HashOK H) (hp : VG.Proof.Pbkdf2.Md.Arm.HmacInit.Pre H sc s₀)
include hH hp

omit hp in
theorem keep_st {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.N⟩ r) : hH.md.stateAt m' p = hH.md.stateAt m p :=
  hH.md.stateAt_congr fun i hi => hf.bytes (R := ⟨p, H.N⟩) hd (by have := hH.sizes.N64; show H.N ≤ 2 ^ 64; omega) hi

omit hp in
theorem keep_repr {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.N + H.B⟩ r) {x : List Byte} (hr : hH.md.Repr hH.iv m p x) :
    hH.md.Repr hH.iv m' p x :=
  hH.md.repr_congr (by have hH_B_ge := hH.B_ge; omega) (fun i hi => hf.bytes (R := ⟨p, H.N + H.B⟩) hd
    (by have hH_B_le := hH.B_le; have := hH.sizes.N64; show H.N + H.B ≤ 2 ^ 64; omega) hi) hr

theorem correct :
    WP isa H.hmacInit s₀ fun s' => abiPreserved s₀ s' ∧ (initG hH.SH sc).post s₀ s' := by
  have hz := hH.sizes
  obtain ⟨hb, hf, nw, hso, hW, hN, hN4, hB4, hB64, hB, ni, no, nk, hkl⟩ := VG.Proof.Pbkdf2.Md.Arm.HmacInit.bounds hz hp
  have hl := hH.link
  -- Where things are.
  have sNI := VG.Proof.Pbkdf2.Md.Arm.HmacInit.st_sub (H := H) (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) (a := 0) (n := H.N) (by omega_using [])
  have sNO := VG.Proof.Pbkdf2.Md.Arm.HmacInit.st_sub (H := H) (VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀) (a := 0) (n := H.N) (by omega)
  rw [BitVec.add_zero] at sNI sNO
  have sBI := VG.Proof.Pbkdf2.Md.Arm.HmacInit.st_sub (H := H) (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) (a := H.N) (n := H.B) (by omega)
  have sBO := VG.Proof.Pbkdf2.Md.Arm.HmacInit.st_sub (H := H) (VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀) (a := H.N) (n := H.B) (by omega)
  have nb : ∀ (x : BitVec 32), Region.Disjoint ⟨State.addr x, H.N⟩ ⟨State.addr x + BitVec.ofNat 64 H.N, H.B⟩ :=
    fun _ => Offset.base_disjoint _ (Nat.le_refl _) (by omega_using [hB, hN])
  have iv0 : ∀ {m : Mem} {p : Addr}, hH.SH.Repr m p [] → hH.md.stateAt m p = hH.iv := fun h => by
    have := (hl.repr _ _ _ h).1
    rwa [List.length_nil, Nat.zero_div, Md.compressList_zero] at this
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.Arm.HmacInit.pro_ok hz hp) fun s₁ ⟨k₁, r6₁, r7₁⟩ => ?_)
  refine WP.seq (VG.Proof.Pbkdf2.Md.Arm.HmacInit.callInit_ok hz hp hH k₁ (.inl ⟨rfl, rfl⟩) fun s₂ k₂ g₂ _ r₂ => ?_)
  refine WP.seq (VG.Proof.Pbkdf2.Md.Arm.HmacInit.callInit_ok hz hp hH k₂ (.inr ⟨rfl, rfl⟩) fun s₃ k₃ g₃ f₃ r₃ => ?_)
  have r6₃ : s₃.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp s₀ := by rw [g₃ _ (by simp), g₂ _ (by simp), r6₁]
  have r7₃ : s₃.gpr .r7 = BitVec.ofNat 32 (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀) := by rw [g₃ _ (by simp), g₂ _ (by simp), r7₁]
  have vI₃ : hH.md.stateAt s₃.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀)) = hH.iv := by
    rw [VG.Proof.Pbkdf2.Md.Arm.HmacInit.keep_st hH f₃ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hp.i_o.sub_left sNI
      · exact hp.b_i.symm.sub_left sNI), iv0 r₂]
  have vO₃ := iv0 r₃
  refine WP.seq (WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.Arm.HmacInit.fill_ok hz hp k₃ r6₃ r7₃) fun s₄ ⟨k₄, d₄, c₄, e₄, z₄, m₄⟩ => ?_))
  have rep₄ : bytesAt s₄.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) + BitVec.ofNat 64 H.N) H.B = List.replicate H.B 0x36 := by
    rw [m₄, bytesAt_writeBytes_self' (List.length_replicate ..) (by omega_using [hB])]
  have f₄ : Frame [⟨State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) + BitVec.ofNat 64 H.N, H.B⟩] s₃.mem s₄.mem := by
    rw [m₄]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [List.length_replicate]; exact Region.contains_self _ _)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.Arm.HmacInit.keys_ok hz hp k₄ d₄ c₄ e₄ z₄ rep₄) fun s₅ ⟨k₅, f₅, bI₅⟩ => ?_)
  refine WP.mono (VG.Proof.Pbkdf2.Md.Arm.HmacInit.opad_ok hz hp k₅) fun s₆ ⟨k₆, a₆, b₆, c₆, m₆⟩ => ?_
  have hl6 : ((bytesAt s₅.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) + BitVec.ofNat 64 H.N) H.B).map (· ^^^ (0x6a : Byte))).length =
      H.B := by simp [bytesAt_length]
  have f₆ : Frame [⟨State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀) + BitVec.ofNat 64 H.N, H.B⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hl6]; exact Region.contains_self _ _)
  have bO₆ : bytesAt s₆.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀) + BitVec.ofNat 64 H.N) H.B =
      (bytesAt s₅.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) + BitVec.ofNat 64 H.N) H.B).map (· ^^^ 0x6a) := by
    rw [m₆, bytesAt_writeBytes_self' hl6 (by omega_using [hB])]
  have bI₆ : bytesAt s₆.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) + BitVec.ofNat 64 H.N) H.B =
      bytesAt s₅.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) + BitVec.ofNat 64 H.N) H.B :=
    Memory.frame_bytesAt f₆ (by
      simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.sub_left sBI).sub_right sBO) (by omega_using [hB])
  -- The hash values are those `init` left.
  have vI₆ : hH.md.stateAt s₆.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀)) = hH.iv := by
    rw [VG.Proof.Pbkdf2.Md.Arm.HmacInit.keep_st hH f₆ (by
        simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.sub_left sNI).sub_right sBO),
      VG.Proof.Pbkdf2.Md.Arm.HmacInit.keep_st hH f₅ (by simp only [List.mem_singleton]; rintro r rfl; exact nb _),
      VG.Proof.Pbkdf2.Md.Arm.HmacInit.keep_st hH f₄ (by simp only [List.mem_singleton]; rintro r rfl; exact nb _), vI₃]
  have vO₆ : hH.md.stateAt s₆.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀)) = hH.iv := by
    rw [VG.Proof.Pbkdf2.Md.Arm.HmacInit.keep_st hH f₆ (by simp only [List.mem_singleton]; rintro r rfl; exact nb _),
      VG.Proof.Pbkdf2.Md.Arm.HmacInit.keep_st hH f₅ (by
        simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.symm.sub_left sNO).sub_right sBI),
      VG.Proof.Pbkdf2.Md.Arm.HmacInit.keep_st hH f₄ (by
        simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.symm.sub_left sNO).sub_right sBI), vO₃]
  refine WP.seq (VG.Proof.Pbkdf2.Md.Arm.HmacInit.cmpS_ok hz hp hH k₆ (.inl rfl) a₆ b₆ c₆ fun s₇ k₇ r3₇ f₇ e₇ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.Arm.HmacInit.toOuter_ok hz k₇ r3₇) fun s₈ ⟨k₈, a₈, b₈, c₈, m₈⟩ => ?_)
  refine WP.seq (VG.Proof.Pbkdf2.Md.Arm.HmacInit.cmpS_ok hz hp hH k₈ (.inr rfl) a₈ b₈ c₈ fun s₉ k₉ _ f₉ e₉ => ?_)
  -- The key.
  have hK : xorPad (blockKey hH.SH.H (bytesAt s₀.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp s₀)) (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀))) ipad =
      bytesAt s₅.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀) + BitVec.ofNat 64 H.N) H.B := by
    rw [bI₅, MdKeys.blockKey_short _ (by rw [bytesAt_length, hH.hB]; exact hkl), MdKeys.xorPad_short,
      bytesAt_length, hH.hB]
  have hKl : (xorPad (blockKey hH.SH.H (bytesAt s₀.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp s₀)) (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀))) ipad).length = H.B := by
    rw [hK, bytesAt_length]
  -- The inner state.
  have rI₇ := Md.repr_block (H := hH.md) (iv := hH.iv) (by omega_using [hB64]) hKl (by rw [bI₆, hK]) (by rw [e₇, vI₆])
  have dI₉ : ∀ r ∈ [(⟨State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀), H.N⟩ : Region), VG.Proof.Pbkdf2.Md.Arm.HmacInit.cmpR H s₀],
      Region.Disjoint ⟨State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀), H.N + H.B⟩ r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.i_o.sub_right sNO
    · exact hp.i_s.sub_right (VG.Proof.Pbkdf2.Md.Arm.HmacInit.cmp_sub hz hp)
  have rI₉ := VG.Proof.Pbkdf2.Md.Arm.HmacInit.keep_repr hH f₉ dI₉ (m₈ ▸ rI₇)
  -- The outer state.
  have d₇ : ∀ {a n : Nat}, a + n ≤ H.N + H.B → ∀ r ∈ [(⟨State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀), H.N⟩ : Region), VG.Proof.Pbkdf2.Md.Arm.HmacInit.cmpR H s₀],
      Region.Disjoint ⟨State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀) + BitVec.ofNat 64 a, n⟩ r := by
    intro a n h
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact (hp.i_o.symm.sub_left (VG.Proof.Pbkdf2.Md.Arm.HmacInit.st_sub _ h)).sub_right sNI
    · exact (hp.o_s.sub_left (VG.Proof.Pbkdf2.Md.Arm.HmacInit.st_sub _ h)).sub_right (VG.Proof.Pbkdf2.Md.Arm.HmacInit.cmp_sub hz hp)
  have vO₈ : hH.md.stateAt s₈.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀)) = hH.iv := by
    rw [m₈, VG.Proof.Pbkdf2.Md.Arm.HmacInit.keep_st hH f₇ (by have := d₇ (a := 0) (n := H.N) (by omega_using []); rwa [BitVec.add_zero] at this), vO₆]
  have bO₈ : bytesAt s₈.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀) + BitVec.ofNat 64 H.N) H.B =
      xorPad (blockKey hH.SH.H (bytesAt s₀.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp s₀)) (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀))) opad := by
    rw [m₈, Memory.frame_bytesAt f₇ (d₇ (by omega)) (by omega_using [hB]), bO₆, ← hK, MdKeys.xorOpad_ipad]
  have rO₉ := Md.repr_block (H := hH.md) (iv := hH.iv) (by omega)
    (by rw [xorPad_length, ← xorPad_length _ ipad, hKl]) bO₈ (by rw [e₉, vO₈])
  -- The end.
  have hsc : ⟨State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀), 8 * sc⟩ ∈ s₉.wr := by rw [k₉.wr, hp.wr]; simp
  refine WP.mono (VG.Proof.Pbkdf2.Stream.Arm.restore_ok H.st k₉.r11 hW k₉.saved hsc (by omega) nw) fun s' ⟨hm, _, _, hsp, hg, _⟩ => ?_
  refine ⟨⟨fun r hr => hg r (preserved_saved r hr), by rw [hsp, k₉.sp]⟩, ?_⟩
  show hH.SH.Repr s'.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀)) _ ∧ hH.SH.Repr s'.mem (State.addr (VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀)) _
  rw [hm]
  exact ⟨hH.back _ _ _ rI₉, hH.back _ _ _ rO₉⟩

end

end VG.Proof.Pbkdf2.Md.Arm.HmacInit

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.Arm.HmacInitCT`. -/
section

/-!
# HMAC's `init` over a Merkle–Damgård hash function on ARMv7: constant time

As `finalize` (`HmacFinCT.lean`): correctness determines our registers from
the public arguments alone, so the taint analysis proves the blocks between
the calls constant time from them (`Checks`, evaluated for each hash
function); the calls of the streaming `init` are constant time by its own
proof (`init_rel`, `Proof/Pbkdf2/Stream/Arm/Hash.lean`), and those of the
compression function by its own (`compressBlock_rel`).
-/

namespace VG.Proof.Pbkdf2.Md.Arm.HmacInit

open VG VG.Arm
open VG.Impl.Pbkdf2.Md.Arm (Hash)
open VG.Proof.Pbkdf2.Md.Arm
open VG.Proof.Pbkdf2.Stream.Arm (initG init_rel covers_one)

/-- The registers that the pieces between the calls use, which hold our
variables: `inner`, `outer`, the key and its length, and `scratch`. -/
abbrev regsK : List Reg := [.r4, .r5, .r6, .r7, .r11]

/-- The taint checks of the pieces of `init` between its calls, which
depend on the hash function's sizes. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (taint.check (argTaint [.r0, .r1, .r2, .r3] 4) (.block H.initPrologue) hc).isSome = true
  arg : ∀ st ∈ [Reg.r4, .r5], ∃ hc, (taint.check (Taint.ofRegs VG.Proof.Pbkdf2.Md.Arm.HmacInit.regsK) (.block [.mov .r0 (.reg st)]) hc).isSome = true
  blocks : ∃ hc, (taint.check (Taint.ofRegs VG.Proof.Pbkdf2.Md.Arm.HmacInit.regsK) H.blocks hc).isSome = true
  toOuter : ∃ hc, (taint.check (Taint.ofRegs VG.Proof.Pbkdf2.Md.Arm.HmacInit.kregs) (.block H.toOuter) hc).isSome = true
  restore : ∃ hc, (taint.check (Taint.ofRegs VG.Proof.Pbkdf2.Md.Arm.HmacInit.kregs) (.block H.st.restore) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  r0 : s₀.gpr .r0 = s₀'.gpr .r0
  r1 : s₀.gpr .r1 = s₀'.gpr .r1
  r2 : s₀.gpr .r2 = s₀'.gpr .r2
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  a0 : stackArg s₀ 0 = stackArg s₀' 0

section
variable {H : Hash} {sc : Nat} {s₀ s₀' : State}

theorem kr_agree (hq : VG.Proof.Pbkdf2.Md.Arm.HmacInit.PubEq s₀ s₀') {s s' : State} (h : VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s) (h' : VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀' s') :
    ∀ r ∈ VG.Proof.Pbkdf2.Md.Arm.HmacInit.kregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.r4, h'.r4, VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn, VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn, hq.r0]
  · rw [h.r5, h'.r5, VG.Proof.Pbkdf2.Md.Arm.HmacInit.out, VG.Proof.Pbkdf2.Md.Arm.HmacInit.out, hq.r1]
  · rw [h.r11, h'.r11, VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr, VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr, hq.a0]

/-- `KR`, with the key and its length in `r6` and `r7`. -/
def KK (H : Hash) (sc : Nat) (s₀ s : State) : Prop :=
  VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s ∧ s.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp s₀ ∧ s.gpr .r7 = BitVec.ofNat 32 (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl s₀)

theorem kk_agree (hq : VG.Proof.Pbkdf2.Md.Arm.HmacInit.PubEq s₀ s₀') {s s' : State} (h : VG.Proof.Pbkdf2.Md.Arm.HmacInit.KK H sc s₀ s) (h' : VG.Proof.Pbkdf2.Md.Arm.HmacInit.KK H sc s₀' s') :
    ∀ r ∈ VG.Proof.Pbkdf2.Md.Arm.HmacInit.regsK, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact VG.Proof.Pbkdf2.Md.Arm.HmacInit.kr_agree hq h.1 h'.1 _ (by simp)
  · exact VG.Proof.Pbkdf2.Md.Arm.HmacInit.kr_agree hq h.1 h'.1 _ (by simp)
  · rw [h.2.1, h'.2.1, VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp, VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp, hq.r2]
  · rw [h.2.2, h'.2.2, VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl, VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl, hq.r3]
  · exact VG.Proof.Pbkdf2.Md.Arm.HmacInit.kr_agree hq h.1 h'.1 _ (by simp)

end

section
variable {H : Hash} (hH : VG.Proof.Pbkdf2.Md.Arm.HashOK H) {sc : Nat} {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Md.Arm.HmacInit.Pre H sc s₀) (hp' : VG.Proof.Pbkdf2.Md.Arm.HmacInit.Pre H sc s₀')
  (hq : VG.Proof.Pbkdf2.Md.Arm.HmacInit.PubEq s₀ s₀')
include hH hp hp' hq

/-- A call of the streaming `init` on the state in `st` (`r4` for `inner`,
`r5` for `outer`). -/
theorem callInit_rel (hc : VG.Proof.Pbkdf2.Md.Arm.HmacInit.Checks H) {st : Reg} {p : BitVec 32}
    (hst : st = .r4 ∧ p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀ ∨ st = .r5 ∧ p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀) :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.Arm.HmacInit.KK H sc s₀ s ∧ VG.Proof.Pbkdf2.Md.Arm.HmacInit.KK H sc s₀' s') (H.st.callInit st)
      fun s s' => VG.Proof.Pbkdf2.Md.Arm.HmacInit.KK H sc s₀ s ∧ VG.Proof.Pbkdf2.Md.Arm.HmacInit.KK H sc s₀' s' := by
  have hz := hH.sizes
  have hst' : st = .r4 ∧ p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀' ∨ st = .r5 ∧ p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀' := by
    rcases hst with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, by rw [h2, VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn, VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn, hq.r0]⟩
    · exact .inr ⟨h1, by rw [h2, VG.Proof.Pbkdf2.Md.Arm.HmacInit.out, VG.Proof.Pbkdf2.Md.Arm.HmacInit.out, hq.r1]⟩
  have hpR : p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀ ∨ p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀ := by rcases hst with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  have hpR' : p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀' ∨ p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀' := by rcases hst' with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  obtain ⟨_, _, _, np, hin⟩ := VG.Proof.Pbkdf2.Md.Arm.HmacInit.st_facts hz hp hpR
  obtain ⟨_, _, _, _, hin'⟩ := VG.Proof.Pbkdf2.Md.Arm.HmacInit.st_facts hz hp' hpR'
  have hS : H.st.S = H.N + H.B := hz.S
  let F : State → State → Prop := fun t₀ s => VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc t₀ s ∧ s.gpr .r0 = p ∧ s.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.kp t₀ ∧
    s.gpr .r7 = BitVec.ofNat 32 (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kl t₀)
  have ha : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.Arm.HmacInit.KK H sc s₀ s ∧ VG.Proof.Pbkdf2.Md.Arm.HmacInit.KK H sc s₀' s') (.block [.mov .r0 (.reg st)])
      fun s s' => F s₀ s ∧ F s₀' s' :=
    rel_agree (Taint.ofRegs VG.Proof.Pbkdf2.Md.Arm.HmacInit.regsK) (fun _ _ h h' => Taint.agree_ofRegs (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kk_agree hq h h'))
      (hc.arg st (by rcases hst with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp))
      (fun _ ⟨k, r6, r7⟩ => WP.mono (VG.Proof.Pbkdf2.Md.Arm.HmacInit.initArg_ok k hst) fun _ ⟨k', d, g, _⟩ =>
        ⟨k', d, by rw [g _ (by simp), r6], by rw [g _ (by simp), r7]⟩)
      (fun _ ⟨k, r6, r7⟩ => WP.mono (VG.Proof.Pbkdf2.Md.Arm.HmacInit.initArg_ok k hst') fun _ ⟨k', d, g, _⟩ =>
        ⟨k', d, by rw [g _ (by simp), r6], by rw [g _ (by simp), r7]⟩)
  unfold Impl.Pbkdf2.Stream.Arm.Hash.callInit
  refine ha.seq (rel_wp (init_rel hH.stream (st := p) fun s s' ⟨⟨k, d, _⟩, ⟨k', d', _⟩⟩ =>
      ⟨d, d', by rw [hS]; exact np, by rw [k.wr, hS]; exact covers_one hin, by rw [k'.wr, hS]; exact covers_one hin'⟩)
    (fun _ ⟨k, d, r6, r7⟩ => VG.Proof.Pbkdf2.Md.Arm.HmacInit.initCall_ok hz hp hH k hpR d fun _ k' g _ _ =>
      ⟨k', by rw [g _ (by simp), r6], by rw [g _ (by simp), r7]⟩)
    (fun _ ⟨k, d, r6, r7⟩ => VG.Proof.Pbkdf2.Md.Arm.HmacInit.initCall_ok hz hp' hH k hpR' d fun _ k' g _ _ =>
      ⟨k', by rw [g _ (by simp), r6], by rw [g _ (by simp), r7]⟩))

/-- The compression of the buffer of the state at `p`. -/
theorem cmpS_rel {p p' : BitVec 32} (hpR : p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀ ∨ p = VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀) (hpR' : p' = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀' ∨ p' = VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀')
    (he : p' = p) :
    RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s ∧ s.gpr .r0 = p ∧ s.gpr .r3 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀ ∧
          s.gpr .r6 = p + BitVec.ofNat 32 H.N) ∧
        (VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀' s' ∧ s'.gpr .r0 = p' ∧ s'.gpr .r3 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀' ∧ s'.gpr .r6 = p' + BitVec.ofNat 32 H.N))
      H.compressBlock fun s s' => (VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s ∧ s.gpr .r3 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀) ∧ (VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀' s' ∧ s'.gpr .r3 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀') := by
  have hz := hH.sizes
  have e : VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀' = VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀ := hq.a0.symm
  exact rel_wp (VG.Proof.Pbkdf2.Md.Arm.compressBlock_rel (H := hH.md) (so := H.so) hH.comp (name := H.compN) (st := p) (scr := VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀)
      (src := p + BitVec.ofNat 32 H.N) fun s s' ⟨⟨k, a, b, c⟩, ⟨k', a', b', c'⟩⟩ => by
        have c₂ := VG.Proof.Pbkdf2.Md.Arm.HmacInit.callOk hz hp' k' hpR' a' b' c'
        rw [he, e] at c₂
        exact ⟨VG.Proof.Pbkdf2.Md.Arm.HmacInit.callOk hz hp k hpR a b c, c₂⟩)
    (fun _ ⟨k, a, b, c⟩ => VG.Proof.Pbkdf2.Md.Arm.HmacInit.cmpS_ok hz hp hH k hpR a b c fun _ k' r3 _ _ => ⟨k', r3⟩)
    (fun _ ⟨k, a, b, c⟩ => VG.Proof.Pbkdf2.Md.Arm.HmacInit.cmpS_ok hz hp' hH k hpR' a b c fun _ k' r3 _ _ => ⟨k', r3⟩)

include hH hp hp' hq in
theorem ct (hc : VG.Proof.Pbkdf2.Md.Arm.HmacInit.Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacInit fun _ _ => True := by
  have hz := hH.sizes
  have aw : ∀ {t : State}, VG.Proof.Pbkdf2.Md.Arm.HmacInit.Pre H sc t →
      t.sp.toNat + 4 ≤ 2 ^ 32 ∧ ∀ r ∈ t.wr, Region.Disjoint ⟨State.addr t.sp, 4⟩ r := fun {t} h => by
    have e : (⟨State.addr t.sp, 4⟩ : Region) = VG.Proof.Pbkdf2.Md.Arm.HmacInit.argR t := by simp [stackArgAddr]
    refine ⟨h.spf, ?_⟩
    simp only [e, h.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact h.a_i
    · exact h.a_o
    · exact h.a_s
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.initPrologue)
      fun s s' => VG.Proof.Pbkdf2.Md.Arm.HmacInit.KK H sc s₀ s ∧ VG.Proof.Pbkdf2.Md.Arm.HmacInit.KK H sc s₀' s' :=
    rel_agree (argTaint [.r0, .r1, .r2, .r3] 4) (fun s s' e e' => by
        rw [e, e']
        refine agree_argTaint (fun r hr => ?_) hq.sp (aw hp) (aw hp')
          (argMem_of (j := 1) hq.sp hp.spf fun i hi => by rw [show i = 0 by omega]; exact hq.a0)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.r0
        · exact hq.r1
        · exact hq.r2
        · exact hq.r3) hc.pro
      (fun _ e => by rw [e]; exact VG.Proof.Pbkdf2.Md.Arm.HmacInit.pro_ok hz hp)
      (fun _ e => by rw [e]; exact VG.Proof.Pbkdf2.Md.Arm.HmacInit.pro_ok hz hp')
  have blk : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.Arm.HmacInit.KK H sc s₀ s ∧ VG.Proof.Pbkdf2.Md.Arm.HmacInit.KK H sc s₀' s') H.blocks
      fun s s' => (VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s ∧ s.gpr .r0 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀ ∧ s.gpr .r3 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀ ∧
          s.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀ + BitVec.ofNat 32 H.N) ∧
        (VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀' s' ∧ s'.gpr .r0 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀' ∧ s'.gpr .r3 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀' ∧ s'.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.inn s₀' + BitVec.ofNat 32 H.N) :=
    rel_agree (Taint.ofRegs VG.Proof.Pbkdf2.Md.Arm.HmacInit.regsK) (fun _ _ h h' => Taint.agree_ofRegs (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kk_agree hq h h')) hc.blocks
      (fun _ ⟨k, r6, r7⟩ => VG.Proof.Pbkdf2.Md.Arm.HmacInit.blocks_ok hz hp k r6 r7)
      (fun _ ⟨k, r6, r7⟩ => VG.Proof.Pbkdf2.Md.Arm.HmacInit.blocks_ok hz hp' k r6 r7)
  have tO : RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s ∧ s.gpr .r3 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀) ∧ (VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀' s' ∧ s'.gpr .r3 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀'))
      (.block H.toOuter)
      fun s s' => (VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s ∧ s.gpr .r0 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀ ∧ s.gpr .r3 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀ ∧
          s.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀ + BitVec.ofNat 32 H.N) ∧
        (VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀' s' ∧ s'.gpr .r0 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀' ∧ s'.gpr .r3 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀' ∧ s'.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.out s₀' + BitVec.ofNat 32 H.N) :=
    rel_agree (Taint.ofRegs VG.Proof.Pbkdf2.Md.Arm.HmacInit.kregs) (fun _ _ h h' => Taint.agree_ofRegs (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kr_agree hq h.1 h'.1)) hc.toOuter
      (fun _ ⟨k, r3⟩ => WP.mono (VG.Proof.Pbkdf2.Md.Arm.HmacInit.toOuter_ok hz k r3) fun _ ⟨k', a, b, c, _⟩ => ⟨k', a, b, c⟩)
      (fun _ ⟨k, r3⟩ => WP.mono (VG.Proof.Pbkdf2.Md.Arm.HmacInit.toOuter_ok hz k r3) fun _ ⟨k', a, b, c, _⟩ => ⟨k', a, b, c⟩)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀ s ∧ s.gpr .r3 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀) ∧ (VG.Proof.Pbkdf2.Md.Arm.HmacInit.KR H sc s₀' s' ∧ s'.gpr .r3 = VG.Proof.Pbkdf2.Md.Arm.HmacInit.scr s₀'))
      (.block H.st.restore) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Pbkdf2.Md.Arm.HmacInit.kregs) (fun _ _ h => Taint.agree_ofRegs (VG.Proof.Pbkdf2.Md.Arm.HmacInit.kr_agree hq h.1.1 h.2.1)) hr
  exact pro.seq ((VG.Proof.Pbkdf2.Md.Arm.HmacInit.callInit_rel hH hp hp' hq hc (.inl ⟨rfl, rfl⟩)).seq
    ((VG.Proof.Pbkdf2.Md.Arm.HmacInit.callInit_rel hH hp hp' hq hc (.inr ⟨rfl, rfl⟩)).seq
    (blk.seq ((VG.Proof.Pbkdf2.Md.Arm.HmacInit.cmpS_rel hH hp hp' hq (.inl rfl) (.inl rfl) hq.r0.symm).seq
    (tO.seq ((VG.Proof.Pbkdf2.Md.Arm.HmacInit.cmpS_rel hH hp hp' hq (.inr rfl) (.inr rfl) hq.r1.symm).seq restore))))))

end

/-! ## Verified -/

theorem pubEq_of {S : Spec.Hmac.StreamingHash} {W : Nat} {s₁ s₂ : State} (h : (initG S W).pub s₁ s₂) :
    VG.Proof.Pbkdf2.Md.Arm.HmacInit.PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- HMAC's `init` is verified against `initG`, for any hash function the
proof supports (`HashOK`), whose pieces of code the taint analysis accepts
(`Checks`). -/
theorem verified {H : Hash} (hH : VG.Proof.Pbkdf2.Md.Arm.HashOK H) (hc : VG.Proof.Pbkdf2.Md.Arm.HmacInit.Checks H) {sc : Nat} (hfit : H.st.buf ≤ 8 * sc)
    (hsat : ∃ s, (initG hH.SH sc).pre s) :
    Verified Arm.target H.hmacInit (initG hH.SH sc) := by
  refine ⟨fun s hs => VG.Proof.Pbkdf2.Md.Arm.HmacInit.correct hH (VG.Proof.Pbkdf2.Md.Arm.HmacInit.pre_of hH hs hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  exact (VG.Proof.Pbkdf2.Md.Arm.HmacInit.ct hH (VG.Proof.Pbkdf2.Md.Arm.HmacInit.pre_of hH h₁ hfit) (VG.Proof.Pbkdf2.Md.Arm.HmacInit.pre_of hH h₂ hfit) (VG.Proof.Pbkdf2.Md.Arm.HmacInit.pubEq_of hpub) hc _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.Arm.HmacInit

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Iterate`. -/
section

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on ARMv7

The same proof as on x86-64 and AArch64 (`Proof/Pbkdf2/AArch64/Iterate.lean`):
the iteration (`Impl/Pbkdf2/Md/Arm.lean`) is correct for any hash function the
generic streaming proofs describe (`Md`), whose digest code and length field
are as `HashOK` says, with any correct compression function (`CompOk`), used
as a black box through its proof; `Md.hmac_step` says that its two
compressions per step compute HMAC. The contract is `iterG`
(`Proof/Pbkdf2/Stream/Arm/Hash.lean`), the shared one's at 16 bytes of stack,
although the function uses none.
-/

namespace VG.Proof.Pbkdf2.Md.Arm.Iterate

open VG VG.Arm
open VG.Impl.Pbkdf2.Md.Arm (Hash copyW padFrom constW xorW lenWords)
open VG.Proof.Pbkdf2.Md.Arm
open VG.Proof.MdStream (Md)
open VG.Proof.Pbkdf2.Stream.Arm (iterG below SavedRegs saveR savedRegs preserved_saved)
open VG.Proof.MdStream.Arm (Upd Fupd wp_mov wp_ldrSp wp_cmp wp_subs op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero sub_ofNat)
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.Hmac.Common (bytesAt_add bytesAt_length bytesAt_writeBytes_sep writeBytes_at bytesAt_getD')
open VG.Proof.Hmac.Generic.Common (bytesAt_take bytesAt_writeBytes_self')
open VG.Spec.Hmac (xorPad ipad opad hmacBlockKey)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev key : BitVec 32 := s₀.gpr .r0
abbrev up : BitVec 32 := s₀.gpr .r1
/-- The number of steps. -/
abbrev nn : Nat := (s₀.gpr .r2).toNat
abbrev tp : BitVec 32 := s₀.gpr .r3
abbrev scr : BitVec 32 := stackArg s₀ 0
abbrev kA : Addr := State.addr (VG.Proof.Pbkdf2.Md.Arm.Iterate.key s₀)
abbrev uA : Addr := State.addr (VG.Proof.Pbkdf2.Md.Arm.Iterate.up s₀)
abbrev tA : Addr := State.addr (VG.Proof.Pbkdf2.Md.Arm.Iterate.tp s₀)
abbrev scA : Addr := State.addr (VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀)
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩

end

section
variable (H : Hash) (sc : Nat) (s₀ : State)

abbrev keyR : Region := ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.kA s₀, 2 * (H.N + H.B)⟩
abbrev uR : Region := ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.uA s₀, H.D⟩
abbrev tR : Region := ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.tA s₀, H.D⟩
abbrev scR : Region := ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.scA s₀, 8 * sc⟩
/-- The hash value being compressed and the block, as registers hold them. -/
abbrev hv : BitVec 32 := VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀ + BitVec.ofNat 32 H.hvO
abbrev blk : BitVec 32 := VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀ + BitVec.ofNat 32 H.blkO
/-- And as addresses. -/
abbrev hvA : Addr := VG.Proof.Pbkdf2.Md.Arm.Iterate.scA s₀ + BitVec.ofNat 64 H.hvO
abbrev blkA : Addr := VG.Proof.Pbkdf2.Md.Arm.Iterate.scA s₀ + BitVec.ofNat 64 H.blkO

end

structure Pre (H : Hash) (sc : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Pbkdf2.Md.Arm.Iterate.keyR H s₀, VG.Proof.Pbkdf2.Md.Arm.Iterate.uR H s₀, VG.Proof.Pbkdf2.Md.Arm.Iterate.argR s₀]
  wr : s₀.wr = [VG.Proof.Pbkdf2.Md.Arm.Iterate.tR H s₀, VG.Proof.Pbkdf2.Md.Arm.Iterate.scR sc s₀]
  k_t : (VG.Proof.Pbkdf2.Md.Arm.Iterate.keyR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.Iterate.tR H s₀)
  k_s : (VG.Proof.Pbkdf2.Md.Arm.Iterate.keyR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.Iterate.scR sc s₀)
  u_t : (VG.Proof.Pbkdf2.Md.Arm.Iterate.uR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.Iterate.tR H s₀)
  u_s : (VG.Proof.Pbkdf2.Md.Arm.Iterate.uR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.Iterate.scR sc s₀)
  t_s : (VG.Proof.Pbkdf2.Md.Arm.Iterate.tR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.Iterate.scR sc s₀)
  a_t : (VG.Proof.Pbkdf2.Md.Arm.Iterate.argR s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.Iterate.tR H s₀)
  a_s : (VG.Proof.Pbkdf2.Md.Arm.Iterate.argR s₀).Disjoint (VG.Proof.Pbkdf2.Md.Arm.Iterate.scR sc s₀)
  nk : (VG.Proof.Pbkdf2.Md.Arm.Iterate.key s₀).toNat + 2 * (H.N + H.B) ≤ 2 ^ 32
  nu : (VG.Proof.Pbkdf2.Md.Arm.Iterate.up s₀).toNat + H.D ≤ 2 ^ 32
  nt : (VG.Proof.Pbkdf2.Md.Arm.Iterate.tp s₀).toNat + H.D ≤ 2 ^ 32
  ns : (VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  spf : s₀.sp.toNat + 4 ≤ 2 ^ 32
  fits : H.st.buf + H.N + H.B ≤ 8 * sc

theorem pre_of {H : Hash} (hH : VG.Proof.Pbkdf2.Md.Arm.HashOK H) {sc : Nat} {s₀ : State} (h : (iterG hH.SH sc).pre s₀)
    (hfit : H.st.buf + H.N + H.B ≤ 8 * sc) : VG.Proof.Pbkdf2.Md.Arm.Iterate.Pre H sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, -, -, -, -, h13, h14, h15, h16, -, h18⟩ := h
  have hS := hH.hS
  have hD := hH.hD
  simp only [hS, hD] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h13, h14, h15, h16, h18, hfit⟩

/-! ## The parts of the scratch space -/

theorem buf_eq (H : Hash) : H.st.buf = 8 * H.st.W + 36 := rfl

section
variable {H : Hash} {sc : Nat} (hz : VG.Proof.Pbkdf2.Md.Arm.Sizes H) {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.Arm.Iterate.Pre H sc s₀)
include hz hp

omit hz hp in
theorem scr_sub {a n : Nat} (h : a + n ≤ 8 * sc) :
    Region.Sub ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.scA s₀ + BitVec.ofNat 64 a, n⟩ (VG.Proof.Pbkdf2.Md.Arm.Iterate.scR sc s₀) :=
  Offset.sub_base _ h

omit hz in
theorem in_scr {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ 8 * sc) :
    InRegions s.wr (VG.Proof.Pbkdf2.Md.Arm.Iterate.scA s₀ + BitVec.ofNat 64 a) n :=
  ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.scR sc s₀, by simp [hwr, hp.wr], Offset.contains_base _ h (by have hp_ns := hp.ns; omega)⟩

omit hz in
theorem in_scr' {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ 8 * sc) :
    InRegions (s.rd ++ s.wr) (VG.Proof.Pbkdf2.Md.Arm.Iterate.scA s₀ + BitVec.ofNat 64 a) n := by
  obtain ⟨r, hr, hc⟩ := VG.Proof.Pbkdf2.Md.Arm.Iterate.in_scr hp hwr h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

omit hz in
/-- `scratch` plus an offset within it, as an address. -/
theorem addr_sO {o : Nat} (h : o < 8 * sc) :
    State.addr (VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀ + BitVec.ofNat 32 o) = VG.Proof.Pbkdf2.Md.Arm.Iterate.scA s₀ + BitVec.ofNat 64 o :=
  addr_add (by have hp_ns := hp.ns; omega)

omit hz in
theorem toNat_sO {o : Nat} (h : o < 8 * sc) : (VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀ + BitVec.ofNat 32 o).toNat = (VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀).toNat + o := by
  have hp_ns := hp.ns
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem addr_hv : State.addr (VG.Proof.Pbkdf2.Md.Arm.Iterate.hv H s₀) = VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀ := by
  have hp_fits := hp.fits; have hz_N64 := hz.N64; have : 64 ≤ H.B := by rcases hz.B with h | h <;> omega
  exact VG.Proof.Pbkdf2.Md.Arm.Iterate.addr_sO hp (by simp only [Hash.hvO]; omega_using [this, hp_fits])

theorem addr_blk : State.addr (VG.Proof.Pbkdf2.Md.Arm.Iterate.blk H s₀) = VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ := by
  have hp_fits := hp.fits; have hz_N64 := hz.N64; have : 64 ≤ H.B := by rcases hz.B with h | h <;> omega
  exact VG.Proof.Pbkdf2.Md.Arm.Iterate.addr_sO hp (by simp only [Hash.blkO]; omega_using [this, hp_fits])

omit hz in
theorem in_blk {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ H.B) :
    InRegions s.wr (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 a) n := by
  have hp_fits := hp.fits
  rw [Memory.add_ofNat]; exact VG.Proof.Pbkdf2.Md.Arm.Iterate.in_scr hp hwr (by simp only [Hash.blkO]; omega)

end

/-! ## The registers during a step -/

/-- The registers `iterate` keeps between its pieces (but the count). -/
abbrev kept : List Reg := [.r0, .r3, .r4, .r6, .r7, .r11]

theorem kept_pres : ∀ r ∈ VG.Proof.Pbkdf2.Md.Arm.Iterate.kept, r ≠ .r0 → r ≠ .r3 → r ∈ preserved ∧ r ≠ .lr := by decide
theorem ne12 : ∀ r ∈ VG.Proof.Pbkdf2.Md.Arm.Iterate.kept, r ≠ .r12 := by decide
theorem ne1 : ∀ r ∈ VG.Proof.Pbkdf2.Md.Arm.Iterate.kept, r ≠ .r1 := by decide
theorem ne5 : ∀ r ∈ VG.Proof.Pbkdf2.Md.Arm.Iterate.kept, r ≠ .r5 := by decide
theorem ne9 : ∀ r ∈ VG.Proof.Pbkdf2.Md.Arm.Iterate.kept, r ≠ .r9 := by decide
theorem ne10 : ∀ r ∈ VG.Proof.Pbkdf2.Md.Arm.Iterate.kept, r ≠ .r10 := by decide

/-- What holds between the pieces of a step: the regions, our registers,
the stack pointer, and memory outside `T` and the scratch space as on entry. -/
structure Regs (H : Hash) (sc : Nat) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r0 : s.gpr .r0 = VG.Proof.Pbkdf2.Md.Arm.Iterate.hv H s₀
  r3 : s.gpr .r3 = VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀
  r4 : s.gpr .r4 = VG.Proof.Pbkdf2.Md.Arm.Iterate.key s₀
  r6 : s.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.Iterate.blk H s₀
  r7 : s.gpr .r7 = VG.Proof.Pbkdf2.Md.Arm.Iterate.tp s₀
  r11 : s.gpr .r11 = VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀
  frame : Frame [VG.Proof.Pbkdf2.Md.Arm.Iterate.tR H s₀, VG.Proof.Pbkdf2.Md.Arm.Iterate.scR sc s₀] s₀.mem s.mem

section
variable {H : Hash} {sc : Nat} {s₀ : State}

/-- `Regs` after code that keeps our registers and writes only memory in the
regions it allows. -/
theorem Regs.write {s s' : State} (h : VG.Proof.Pbkdf2.Md.Arm.Iterate.Regs H sc s₀ s) (hg : ∀ r ∈ VG.Proof.Pbkdf2.Md.Arm.Iterate.kept, s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hm : Frame [VG.Proof.Pbkdf2.Md.Arm.Iterate.tR H s₀, VG.Proof.Pbkdf2.Md.Arm.Iterate.scR sc s₀] s.mem s'.mem) : VG.Proof.Pbkdf2.Md.Arm.Iterate.Regs H sc s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  sp := hsp.trans h.sp
  r0 := (hg _ (by decide)).trans h.r0
  r3 := (hg _ (by decide)).trans h.r3
  r4 := (hg _ (by decide)).trans h.r4
  r6 := (hg _ (by decide)).trans h.r6
  r7 := (hg _ (by decide)).trans h.r7
  r11 := (hg _ (by decide)).trans h.r11
  frame := h.frame.trans hm

/-- A part of the scratch space, as a frame of `Regs`. -/
theorem frame_scr {m m' : Mem} {a n : Nat} (h : a + n ≤ 8 * sc)
    (hf : Frame [⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.scA s₀ + BitVec.ofNat 64 a, n⟩] m m') : Frame [VG.Proof.Pbkdf2.Md.Arm.Iterate.tR H s₀, VG.Proof.Pbkdf2.Md.Arm.Iterate.scR sc s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.scR sc s₀, by simp, VG.Proof.Pbkdf2.Md.Arm.Iterate.scr_sub h⟩

end

theorem add0 (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

section
variable {H : Hash} {sc : Nat} (hz : VG.Proof.Pbkdf2.Md.Arm.Sizes H) {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.Arm.Iterate.Pre H sc s₀)
include hz hp

/-- The hash value at `key + o` into the hash value being compressed. -/
theorem load_ok {md : Md H.B H.N H.L} (hR : md.Reloc) {s : State} (h : VG.Proof.Pbkdf2.Md.Arm.Iterate.Regs H sc s₀ s) {o : Nat}
    (ho : o + H.N ≤ 2 * (H.N + H.B)) (ho4 : o % 4 = 0) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀, H.N⟩] s.mem s'.mem →
      md.stateAt s'.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀) = md.stateAt s₀.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.kA s₀ + BitVec.ofNat 64 o) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (H.loadKey o ++ rest)) s Q := by
  have hz_N64 := hz.N64; have hz_N4 := hz.N4; have hp_fits := hp.fits; have hp_nk := hp.nk; have hp_ns := hp.ns; have hB := hz.B
  have hn : 4 * (H.N / 4) = H.N := by omega
  have ahv := VG.Proof.Pbkdf2.Md.Arm.Iterate.addr_hv hz hp
  unfold Hash.loadKey
  refine VG.Proof.Pbkdf2.Md.Arm.copyW_ok (by decide) (by decide) o 0 (H.N / 4) ⟨by omega_using [hB, hz_N64, ho], by omega⟩ rest s Q
    (by rw [h.r4]; omega) (by rw [h.r0, VG.Proof.Pbkdf2.Md.Arm.Iterate.toNat_sO hp (by simp only [Hash.hvO]; omega_using [hB, hp_fits])]; simp only [Hash.hvO]; omega_using [hp_ns, hp_fits])
    (fun j hj => ?_) (fun j hj => ?_) ?_ fun s' g' rd' wr' sp' m' => ?_
  · rw [h.r4, h.rd, hp.rd, Memory.add_ofNat]
    exact ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.keyR H s₀, by simp, Offset.contains_base _ (by omega_using [hj, ho]) (by omega_using [hj, hp_nk, ho])⟩
  · rw [h.r0, ahv, h.wr, Memory.add_ofNat, show VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀ = VG.Proof.Pbkdf2.Md.Arm.Iterate.scA s₀ + BitVec.ofNat 64 H.hvO from rfl,
      Memory.add_ofNat]
    exact VG.Proof.Pbkdf2.Md.Arm.Iterate.in_scr hp rfl (by simp only [Hash.hvO]; omega)
  · rw [h.r4, h.r0, ahv, hn, VG.Proof.Pbkdf2.Md.Arm.Iterate.add0]
    exact hp.k_s.sep (Offset.contains_base _ (by omega) (by omega_using [hp_nk, ho]))
      (Offset.contains_base _ (by simp only [Hash.hvO]; omega_using [hp_fits]) (by simp only [Hash.hvO]; omega_using [hp_ns, hp_fits]))
  rw [h.r0, ahv, h.r4, hn, VG.Proof.Pbkdf2.Md.Arm.Iterate.add0] at m'
  refine k s' g' rd' wr' sp' (by rw [m']; exact VG.WriteBytes.writeBytes_frame _ _ _ (by
    rw [bytesAt_length]; exact Region.contains_self _ _)) ?_
  refine hR _ _ _ _ fun i hi => ?_
  rw [m', writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega_using [hz_N64]),
    bytesAt_getD' _ _ hi, Memory.add_ofNat]
  exact h.frame.bytes (R := VG.Proof.Pbkdf2.Md.Arm.Iterate.keyR H s₀) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.k_t
    · exact hp.k_s) (by show 2 * (H.N + H.B) ≤ 2 ^ 64; omega_using [hp_nk]) (by show o + i < 2 * (H.N + H.B); omega_using [hi, ho])

/-- What the call of the compression function needs. -/
theorem callOk_of {s : State} (h : VG.Proof.Pbkdf2.Md.Arm.Iterate.Regs H sc s₀ s) :
    VG.Proof.Pbkdf2.Md.Arm.CallOk s H.N H.B H.so (VG.Proof.Pbkdf2.Md.Arm.Iterate.hv H s₀) (VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀) (VG.Proof.Pbkdf2.Md.Arm.Iterate.blk H s₀) := by
  have hz_N64 := hz.N64; have hp_fits := hp.fits; have hp_ns := hp.ns; have hz_so := hz.so; have hB := hz.B
  have hsc : VG.Proof.Pbkdf2.Md.Arm.Iterate.scR sc s₀ ∈ s.wr := by simp [h.wr, hp.wr]
  rw [VG.Proof.Pbkdf2.Md.Arm.Iterate.buf_eq H] at *
  refine ⟨h.r0, h.r3, h.r6, by rw [VG.Proof.Pbkdf2.Md.Arm.Iterate.toNat_sO hp (by simp only [Hash.hvO, VG.Proof.Pbkdf2.Md.Arm.Iterate.buf_eq H]; omega)]; simp only [Hash.hvO, VG.Proof.Pbkdf2.Md.Arm.Iterate.buf_eq H]; omega,
    by rw [VG.Proof.Pbkdf2.Md.Arm.Iterate.toNat_sO hp (by simp only [Hash.blkO, VG.Proof.Pbkdf2.Md.Arm.Iterate.buf_eq H]; omega)]; simp only [Hash.blkO, VG.Proof.Pbkdf2.Md.Arm.Iterate.buf_eq H]; omega,
    by omega, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [VG.Proof.Pbkdf2.Md.Arm.Iterate.addr_hv hz hp, VG.Proof.Pbkdf2.Md.Arm.Iterate.addr_blk hz hp, VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA, VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA, Hash.hvO, Hash.blkO, VG.Proof.Pbkdf2.Md.Arm.Iterate.buf_eq H]
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Offset.disjoint _ (.inr (by omega_using [])) (by omega) (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · refine Covers.of_sub fun r hr => ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.scR sc s₀, List.mem_append_right _ hsc, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, rfl, by dsimp only; omega⟩
    · exact ⟨_, rfl, by dsimp only; omega⟩
    · exact ⟨0, by simp, by dsimp only; omega⟩
  · refine Covers.of_sub fun r hr => ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.scR sc s₀, hsc, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, rfl, by dsimp only; omega⟩
    · exact ⟨0, by simp, by dsimp only; omega⟩

/-- A call of the compression function on the block. -/
theorem cmp_ok {md : Md H.B H.N H.L} {name : String} {code : Prog isa} (hf : VG.Proof.Pbkdf2.Md.Arm.CompOk md H.so code) {s : State}
    (h : VG.Proof.Pbkdf2.Md.Arm.Iterate.Regs H sc s₀ s) {Q : State → Prop}
    (k : ∀ s', VG.Proof.Pbkdf2.Md.Arm.Iterate.Regs H sc s₀ s' → s'.gpr .r5 = s.gpr .r5 →
      Frame [⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀, H.N⟩, ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.scA s₀, H.so⟩] s.mem s'.mem →
      md.stateAt s'.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀) = md.compress (md.stateAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀)) (md.blockAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀)) →
      Q s') :
    WP isa (VG.Proof.Pbkdf2.Md.Arm.compressBlock name code) s Q := by
  have hz_N64 := hz.N64; have hp_fits := hp.fits; have hz_so := hz.so; have hB := hz.B
  refine VG.Proof.Pbkdf2.Md.Arm.compressBlock_ok hf (VG.Proof.Pbkdf2.Md.Arm.Iterate.callOk_of hz hp h) fun s' hrd hwr hcs h0 h3 hsp hfr hst => ?_
  rw [VG.Proof.Pbkdf2.Md.Arm.Iterate.addr_hv hz hp] at hfr
  rw [VG.Proof.Pbkdf2.Md.Arm.Iterate.addr_hv hz hp, VG.Proof.Pbkdf2.Md.Arm.Iterate.addr_blk hz hp] at hst
  refine k s' (h.write (fun r hr => ?_) hrd hwr hsp (hfr.sub fun r hr => ?_))
    (hcs _ (by decide) (by decide)) hfr hst
  · by_cases e0 : r = .r0
    · subst e0; rw [h0, h.r0]
    by_cases e3 : r = .r3
    · subst e3; rw [h3, h.r3]
    exact hcs r (VG.Proof.Pbkdf2.Md.Arm.Iterate.kept_pres r hr e0 e3).1 (VG.Proof.Pbkdf2.Md.Arm.Iterate.kept_pres r hr e0 e3).2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [VG.Proof.Pbkdf2.Md.Arm.Iterate.buf_eq H] at *
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.scR sc s₀, by simp, VG.Proof.Pbkdf2.Md.Arm.Iterate.scr_sub (by simp only [Hash.hvO, VG.Proof.Pbkdf2.Md.Arm.Iterate.buf_eq H]; omega)⟩
    · exact ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.scR sc s₀, by simp, Region.sub_prefix (by omega)⟩

end

/-! ## The digest into the block -/

section
variable {H : Hash} {sc : Nat} (hz : VG.Proof.Pbkdf2.Md.Arm.Sizes H) {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.Arm.Iterate.Pre H sc s₀)
include hz hp

/-- The digest of the hash value into the block's first `D` bytes, the padding after them as it was. -/
theorem digest_ok {md : Md H.B H.N H.L} (ho : VG.Proof.Pbkdf2.Md.Arm.OutOk md H.out) {s : State} (h : VG.Proof.Pbkdf2.Md.Arm.Iterate.Regs H sc s₀ s)
    (hpad : bytesAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.D) = md.tailPad H.D) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → Frame [⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀, H.N⟩] s.mem s'.mem →
      bytesAt s'.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀) H.D = (md.digest (md.stateAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀))).take H.D →
      bytesAt s'.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.D) = md.tailPad H.D → WP isa (.block rest) s' Q) :
    WP isa (.block (H.digest ++ rest)) s Q := by
  have hz_N64 := hz.N64; have hp_fits := hp.fits; have hz_DN := hz.DN; have hz_NL := hz.NL; have hz_D4 := hz.D4; have hz_N4 := hz.N4; have hz_pad := hz.pad
  have hp_ns := hp.ns; have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega_using [h]
  have ahv := VG.Proof.Pbkdf2.Md.Arm.Iterate.addr_hv hz hp; have ablk := VG.Proof.Pbkdf2.Md.Arm.Iterate.addr_blk hz hp
  have tb : (VG.Proof.Pbkdf2.Md.Arm.Iterate.blk H s₀).toNat = (VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀).toNat + H.blkO := VG.Proof.Pbkdf2.Md.Arm.Iterate.toNat_sO hp (by simp only [Hash.blkO]; omega_using [hz_pad, hp_fits])
  unfold Hash.digest
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (ho s ?_ ?_ ?_ ?_ ?_) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, m₁⟩ => ?_
  · rw [h.r0, VG.Proof.Pbkdf2.Md.Arm.Iterate.toNat_sO hp (by simp only [Hash.hvO]; omega_using [hz_pad, hp_fits])]; simp only [Hash.hvO]; omega_using [hp_ns, hp_fits]
  · rw [h.r6, tb]; simp only [Hash.blkO]; omega_using [hp_ns, hz_NL, hp_fits]
  · rw [h.r0, ahv]; exact VG.Proof.Pbkdf2.Md.Arm.Iterate.in_scr' hp h.wr (by simp only [Hash.hvO]; omega_using [hp_fits])
  · rw [h.r6, ablk]; exact VG.Proof.Pbkdf2.Md.Arm.Iterate.in_scr hp h.wr (by simp only [Hash.blkO]; omega_using [hz_NL, hp_fits])
  · rw [h.r0, h.r6, ahv, ablk]; exact Offset.disjoint _ (.inl (by simp only [Hash.hvO, Hash.blkO]; omega))
      (by simp only [Hash.hvO]; omega_using [hp_ns, hp_fits]) (by simp only [Hash.blkO]; omega_using [hp_ns, hp_fits])
  rw [h.r6, ablk, h.r0, ahv] at m₁
  have hdl := md.digest_length (md.stateAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀))
  have f₁ : Frame [⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀, H.N⟩] s.mem s₁.mem := by
    rw [m₁]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hdl]; exact Region.contains_self _ _)
  have b₁ : bytesAt s₁.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀) H.D = (md.digest (md.stateAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀))).take H.D := by
    rw [bytesAt_take _ _ hz.DN, m₁, bytesAt_writeBytes_self' hdl (by omega_using [hz_N64])]
  have r₁ : bytesAt s₁.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 H.N) (H.B - H.N) =
      bytesAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 H.N) (H.B - H.N) := by
    rw [m₁]
    refine bytesAt_writeBytes_sep _ _ ?_ (by omega_using [hp_ns, hp_fits])
    have := Offset.sep (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀) (d := H.N) (n := H.B - H.N) (e := 0) (k := H.N) (.inr (by omega))
      (by omega) (by omega_using [hz_N64])
    rw [VG.Proof.Pbkdf2.Md.Arm.Iterate.add0] at this; rw [hdl]; exact this
  have hsplit : ∀ m : Mem, bytesAt m (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.D) =
      bytesAt m (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 H.D) (H.N - H.D) ++
        bytesAt m (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 H.N) (H.B - H.N) := by
    intro m
    rw [show H.B - H.D = (H.N - H.D) + (H.B - H.N) by omega_using [hz_NL, hz_DN], bytesAt_add, Memory.add_ofNat (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀),
      show H.D + (H.N - H.D) = H.N by omega_using [hz_DN]]
  have hY : bytesAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 H.N) (H.B - H.N) = (md.tailPad H.D).drop (H.N - H.D) := by
    rw [← hpad, hsplit, List.drop_left' (bytesAt_length _ _ _)]
  have g₁' : s₁.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.Iterate.blk H s₀ := by rw [g₁ _ (by decide) (by decide), h.r6]
  by_cases hDN : H.D < H.N
  · simp only [hDN, ↓reduceIte]
    refine VG.Proof.Pbkdf2.Md.Arm.padFrom_ok (a := H.D) (b := H.N) (by omega) (by omega_using [hz_N4, hz_D4]) (by omega_using [hz_N64]) (s := s₁) (p := VG.Proof.Pbkdf2.Md.Arm.Iterate.blk H s₀)
      g₁' (by rw [tb]; simp only [Hash.blkO]; omega_using [hp_ns, hz_NL, hp_fits]) (fun j hj => by rw [ablk]; exact VG.Proof.Pbkdf2.Md.Arm.Iterate.in_blk hp (wr₁.trans h.wr) (by omega_using [hj, hz_NL]))
      fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => k s₂ (fun r h9 h10 h12 => (g₂ r h12).trans (g₁ r h9 h10)) (rd₂.trans rd₁)
        (wr₂.trans wr₁) (sp₂.trans sp₁) ?_ ?_ ?_
    · rw [m₂, ablk]
      refine f₁.trans (VG.WriteBytes.writeBytes_frame _ _ _ ?_)
      simp only [List.length_append, List.length_singleton, List.length_replicate]
      exact Offset.contains_base _ (by omega_using [hDN]) (by omega_using [hz_DN, hz_N64])
    · rw [m₂, ablk, bytesAt_writeBytes_sep _ _ ?_ (by omega), b₁]
      have := Offset.sep (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀) (d := 0) (n := H.D) (e := H.D) (k := H.N - H.D) (.inl (by omega))
        (by omega_using [hz_DN, hz_N64]) (by omega_using [hz_DN, hz_N64])
      rw [VG.Proof.Pbkdf2.Md.Arm.Iterate.add0] at this
      have e : ([0x80] ++ List.replicate (H.N - H.D - 1) 0 : List Byte).length = H.N - H.D := by simp; omega_using [hDN]
      rw [e]; exact this
    · have hfix : [(0x80 : Byte)] ++ List.replicate (H.N - H.D - 1) 0 = (md.tailPad H.D).take (H.N - H.D) :=
        (md.tailPad_take (by omega_using [hDN]) (by omega_using [hz_NL, hz_DN])).symm
      have hfl : ((md.tailPad H.D).take (H.N - H.D)).length = H.N - H.D := by
        rw [List.length_take, md.tailPad_length (by omega_using [hz_pad])]; omega_using [hz_NL]
      rw [hsplit, m₂, ablk, hfix, bytesAt_writeBytes_self' hfl (by omega_using [hz_N64]),
        bytesAt_writeBytes_sep _ _ ?_ (by omega), r₁, hY, List.take_append_drop]
      have := Offset.sep (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀) (d := H.N) (n := H.B - H.N) (e := H.D) (k := H.N - H.D) (.inr (by omega_using [hz_DN]))
        (by omega) (by omega_using [hz_DN, hz_N64])
      rw [hfl]; exact this
  · simp only [hDN, ↓reduceIte, List.nil_append]
    have eDN : H.D = H.N := by omega_using [hDN, hz_DN]
    refine k s₁ (fun r h9 h10 _ => g₁ r h9 h10) rd₁ wr₁ sp₁ f₁ b₁ ?_
    rw [hsplit, r₁, hY, eDN, Nat.sub_self, List.drop_zero]
    simp [bytesAt]

end

/-! ## A step -/


section
variable (H : Hash) (md : Md H.B H.N H.L) (s₀ : State)

/-- A step, as the code computes it, from the key's inner and outer hash values. -/
abbrev stepM : List Byte → List Byte :=
  md.step H.D (md.stateAt s₀.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.kA s₀)) (md.stateAt s₀.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.kA s₀ + BitVec.ofNat 64 (H.N + H.B)))

/-- What the body writes: the compression function's scratch space, the hash
value and the block, and `T`. -/
abbrev bodyR : List Region := [⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.scA s₀, H.so⟩, ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀, H.N + H.B⟩, VG.Proof.Pbkdf2.Md.Arm.Iterate.tR H s₀]

end

/-- The loop invariant, with `r` steps left. -/
structure Inv (H : Hash) (sc : Nat) (md : Md H.B H.N H.L) (s₀ : State) (r : Nat) (s : State) : Prop
    extends VG.Proof.Pbkdf2.Md.Arm.Iterate.Regs H sc s₀ s where
  r5 : s.gpr .r5 = BitVec.ofNat 32 r
  saved : SavedRegs H.st (VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀) s₀ s.mem
  pad : bytesAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.D) = md.tailPad H.D
  le : r ≤ VG.Proof.Pbkdf2.Md.Arm.Iterate.nn s₀
  val : Spec.Pbkdf2.iterate (VG.Proof.Pbkdf2.Md.Arm.Iterate.stepM H md s₀) (VG.Proof.Pbkdf2.Md.Arm.Iterate.nn s₀) (bytesAt s₀.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.uA s₀) H.D) (bytesAt s₀.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.tA s₀) H.D) =
    Spec.Pbkdf2.iterate (VG.Proof.Pbkdf2.Md.Arm.Iterate.stepM H md s₀) r (bytesAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀) H.D) (bytesAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.tA s₀) H.D)

section
variable {H : Hash} {sc : Nat} (hz : VG.Proof.Pbkdf2.Md.Arm.Sizes H) {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.Arm.Iterate.Pre H sc s₀)
include hz hp

/-- The saved registers are outside what the body writes. -/
theorem saved_disj : ∀ r ∈ VG.Proof.Pbkdf2.Md.Arm.Iterate.bodyR H s₀, (saveR H.st (VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀)).Disjoint r := by
  have hz_so := hz.so; have hz_W := hz.W; have hp_fits := hp.fits; have hp_ns := hp.ns
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint_base _ (by omega) (by rw [VG.Proof.Pbkdf2.Md.Arm.Iterate.buf_eq H] at *; omega)
  · exact Offset.disjoint _ (.inl (by simp only [Hash.hvO, VG.Proof.Pbkdf2.Md.Arm.Iterate.buf_eq H]; omega)) (by rw [VG.Proof.Pbkdf2.Md.Arm.Iterate.buf_eq H] at *; omega)
      (by simp only [Hash.hvO]; omega)
  · exact (hp.t_s.sub_right (VG.Proof.Pbkdf2.Md.Arm.Iterate.scr_sub (by rw [VG.Proof.Pbkdf2.Md.Arm.Iterate.buf_eq H] at *; omega))).symm

omit hz hp in
/-- A range of the scratch space from the hash value on, within what the body writes. -/
theorem sub_body {a n : Nat} (h₁ : H.hvO ≤ a) (h₂ : a + n ≤ H.hvO + H.N + H.B) :
    ∃ r' ∈ VG.Proof.Pbkdf2.Md.Arm.Iterate.bodyR H s₀, Region.Sub ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.scA s₀ + BitVec.ofNat 64 a, n⟩ r' :=
  ⟨⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀, H.N + H.B⟩, by simp, Offset.sub _ h₁ (by omega)⟩

/-- A range of the block disjoint from what the compression and loading the hash value write. -/
theorem blk_disj {a n : Nat} (h : a + n ≤ H.B) :
    ∀ r ∈ [⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀, H.N⟩, ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.scA s₀, H.so⟩], Region.Disjoint ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 a, n⟩ r := by
  have hz_so := hz.so; have hp_fits := hp.fits; have hp_ns := hp.ns
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [Memory.add_ofNat]
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (.inr (by simp only [Hash.hvO, Hash.blkO]; omega)) (by simp only [Hash.blkO]; omega)
      (by simp only [Hash.hvO]; omega)
  · exact Offset.disjoint_base _ (by simp only [Hash.blkO, VG.Proof.Pbkdf2.Md.Arm.Iterate.buf_eq H]; omega) (by simp only [Hash.blkO]; omega)

end

section
variable {H : Hash} {sc : Nat} (hz : VG.Proof.Pbkdf2.Md.Arm.Sizes H) {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.Arm.Iterate.Pre H sc s₀)
include hz hp

/-- Loading the key's hash value at `key + o` and compressing the block into it. -/
theorem lc_ok {md : Md H.B H.N H.L} (hR : md.Reloc) {name : String} {code : Prog isa}
    (hf : VG.Proof.Pbkdf2.Md.Arm.CompOk md H.so code) {o : Nat} (ho : o + H.N ≤ 2 * (H.N + H.B)) (ho4 : o % 4 = 0) {s : State}
    (h : VG.Proof.Pbkdf2.Md.Arm.Iterate.Regs H sc s₀ s) (hpad : bytesAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.D) = md.tailPad H.D)
    {c : Prog isa} {Q : State → Prop}
    (k : ∀ s', VG.Proof.Pbkdf2.Md.Arm.Iterate.Regs H sc s₀ s' → s'.gpr .r5 = s.gpr .r5 → Frame (VG.Proof.Pbkdf2.Md.Arm.Iterate.bodyR H s₀) s.mem s'.mem →
      Frame [⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.scA s₀, H.so⟩, ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀, H.N⟩] s.mem s'.mem →
      bytesAt s'.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.D) = md.tailPad H.D →
      bytesAt s'.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀) H.D = bytesAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀) H.D →
      md.stateAt s'.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀) =
        md.compress (md.stateAt s₀.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.kA s₀ + BitVec.ofNat 64 o)) (md.tailBlock H.D (bytesAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀) H.D)) →
      WP isa c s' Q) :
    WP isa (.block (H.loadKey o)) s fun s' => WP isa (.seq (VG.Proof.Pbkdf2.Md.Arm.compressBlock name code) c) s' Q := by
  have hz_N64 := hz.N64; have hp_fits := hp.fits; have hz_so := hz.so; have hz_DN := hz.DN; have hz_pad := hz.pad; have hz_NL := hz.NL
  have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  rw [← List.append_nil (H.loadKey o)]
  refine VG.Proof.Pbkdf2.Md.Arm.Iterate.load_ok hz hp hR h (o := o) ho ho4 fun s₁ g₁ rd₁ wr₁ sp₁ f₁ e₁ => WP.block_nil ?_
  have h₁ := h.write (fun r hr => g₁ r (VG.Proof.Pbkdf2.Md.Arm.Iterate.ne12 r hr)) rd₁ wr₁ sp₁
    (VG.Proof.Pbkdf2.Md.Arm.Iterate.frame_scr (a := H.hvO) (by simp only [Hash.hvO]; omega_using [hp_fits]) f₁)
  refine WP.seq (VG.Proof.Pbkdf2.Md.Arm.Iterate.cmp_ok hz hp hf h₁ fun s₂ h₂ x5₂ f₂ e₂ => ?_)
  have fh₁ : ∀ {a n : Nat}, a + n ≤ H.B → ∀ r ∈ [(⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀, H.N⟩ : Region)],
      Region.Disjoint ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 a, n⟩ r :=
    fun h' r hr => VG.Proof.Pbkdf2.Md.Arm.Iterate.blk_disj hz hp h' r (by simp at hr; simp [hr])
  have p₁ : bytesAt s₁.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.D) = md.tailPad H.D :=
    (Memory.frame_bytesAt f₁ (fh₁ (by omega)) (by omega_using [hB])).trans hpad
  have u₁ : bytesAt s₁.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀) H.D = bytesAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀) H.D := by
    have := Memory.frame_bytesAt f₁ (fh₁ (a := 0) (n := H.D) (by omega_using [hz_pad])) (by omega); rwa [VG.Proof.Pbkdf2.Md.Arm.Iterate.add0] at this
  have u₂ : bytesAt s₂.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀) H.D = bytesAt s₁.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀) H.D := by
    have := Memory.frame_bytesAt f₂ (VG.Proof.Pbkdf2.Md.Arm.Iterate.blk_disj hz hp (a := 0) (n := H.D) (by omega)) (by omega); rwa [VG.Proof.Pbkdf2.Md.Arm.Iterate.add0] at this
  rw [e₁, VG.Proof.Pbkdf2.Md.Arm.blockAt_eq (by omega_using [hz_pad]) p₁, u₁] at e₂
  have f : Frame [⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.scA s₀, H.so⟩, ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀, H.N⟩] s.mem s₂.mem :=
    (f₁.mono (by simp)).trans (f₂.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
  refine k s₂ h₂ (x5₂.trans (g₁ _ (by decide))) (f.sub fun r hr => ?_) f
    ((Memory.frame_bytesAt f₂ (VG.Proof.Pbkdf2.Md.Arm.Iterate.blk_disj hz hp (by omega)) (by omega)).trans p₁) (u₂.trans u₁) e₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.scA s₀, H.so⟩, by simp, fun _ h => h⟩
  · exact ⟨⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀, H.N + H.B⟩, by simp, Region.sub_prefix (by omega)⟩

/-- The end of a step: the digest into the block, `T ← T ⊕ U` and the count. -/
theorem tail_ok {md : Md H.B H.N H.L} (ho : VG.Proof.Pbkdf2.Md.Arm.OutOk md H.out) {s : State} (h : VG.Proof.Pbkdf2.Md.Arm.Iterate.Regs H sc s₀ s)
    (hpad : bytesAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.D) = md.tailPad H.D) {Q : State → Prop}
    (k : ∀ s', VG.Proof.Pbkdf2.Md.Arm.Iterate.Regs H sc s₀ s' → s'.gpr .r5 = s.gpr .r5 - 1 → s'.z = (s.gpr .r5 - 1 == 0) →
      Frame (VG.Proof.Pbkdf2.Md.Arm.Iterate.bodyR H s₀) s.mem s'.mem →
      bytesAt s'.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.D) = md.tailPad H.D →
      bytesAt s'.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀) H.D = (md.digest (md.stateAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀))).take H.D →
      bytesAt s'.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.tA s₀) H.D =
        Spec.Pbkdf2.xorBytes (bytesAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.tA s₀) H.D) ((md.digest (md.stateAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀))).take H.D) →
      Q s') :
    WP isa (.block (H.digest ++ (List.range (H.D / 4)).flatMap xorW ++
      ([.subs .r5 .r5 (.imm 1)] : List Instr))) s Q := by
  have hz_N64 := hz.N64; have hp_fits := hp.fits; have hz_DN := hz.DN; have hz_D4 := hz.D4; have hz_pad := hz.pad; have hz_NL := hz.NL; have hp_ns := hp.ns
  have hp_nt := hp.nt
  have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  rw [List.append_assoc]
  refine VG.Proof.Pbkdf2.Md.Arm.Iterate.digest_ok hz hp ho h hpad fun s₆ g₆ rd₆ wr₆ sp₆ f₆ b₆ p₆ => ?_
  have h₆ := h.write (fun r hr => g₆ r (VG.Proof.Pbkdf2.Md.Arm.Iterate.ne9 r hr) (VG.Proof.Pbkdf2.Md.Arm.Iterate.ne10 r hr) (VG.Proof.Pbkdf2.Md.Arm.Iterate.ne12 r hr)) rd₆ wr₆ sp₆
    (VG.Proof.Pbkdf2.Md.Arm.Iterate.frame_scr (a := H.blkO) (by simp only [Hash.blkO]; omega) f₆)
  have hd : Region.Disjoint (VG.Proof.Pbkdf2.Md.Arm.Iterate.tR H s₀) ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀, H.D⟩ :=
    hp.t_s.sub_right (VG.Proof.Pbkdf2.Md.Arm.Iterate.scr_sub (by simp only [Hash.blkO]; omega_using [hz_pad, hp_fits]))
  have hD4 : 4 * (H.D / 4) = H.D := by omega
  refine VG.Proof.Pbkdf2.Md.Arm.xor_ok (tp := VG.Proof.Pbkdf2.Md.Arm.Iterate.tp s₀) (bp := VG.Proof.Pbkdf2.Md.Arm.Iterate.blk H s₀) (D := H.D) (by rw [VG.Proof.Pbkdf2.Md.Arm.Iterate.addr_blk hz hp]; exact hd) (by omega_using [hz_DN, hz_N64]) hp.nt
    (by rw [VG.Proof.Pbkdf2.Md.Arm.Iterate.toNat_sO hp (by simp only [Hash.blkO]; omega)]; simp only [Hash.blkO]; omega)
    (H.D / 4) (by omega_using []) _ s₆ _ h₆.r6 h₆.r7
    (fun j hj => by
      rw [VG.Proof.Pbkdf2.Md.Arm.Iterate.addr_blk hz hp]
      obtain ⟨r, hr, hc⟩ := VG.Proof.Pbkdf2.Md.Arm.Iterate.in_blk hp h₆.wr (a := 4 * j) (n := 4) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (fun j hj => ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.tR H s₀, by simp [h₆.wr, hp.wr], Offset.contains_base _ (by omega_using [hj]) (by omega)⟩)
    fun s₇ g₇ rd₇ wr₇ sp₇ m₇ => ?_
  rw [hD4, VG.Proof.Pbkdf2.Md.Arm.Iterate.addr_blk hz hp] at m₇
  have hxl : (Spec.Pbkdf2.xorBytes (bytesAt s₆.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.tA s₀) H.D) (bytesAt s₆.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀) H.D)).length = H.D := by
    rw [Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
  have f₇ : Frame [VG.Proof.Pbkdf2.Md.Arm.Iterate.tR H s₀] s₆.mem s₇.mem := by
    rw [m₇]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
  have h₇ := h₆.write (fun r hr => g₇ r (VG.Proof.Pbkdf2.Md.Arm.Iterate.ne12 r hr) (VG.Proof.Pbkdf2.Md.Arm.Iterate.ne1 r hr)) rd₇ wr₇ sp₇ (f₇.mono (by simp))
  refine wp_subs (op2_imm (by decide)) fun s₈ u₈ z₈ => WP.block_nil ?_
  have h₈ := h₇.write (fun r hr => u₈.other r (VG.Proof.Pbkdf2.Md.Arm.Iterate.ne5 r hr)) u₈.rd u₈.wr u₈.sp (by rw [u₈.mem]; exact Frame.refl _ _)
  have x5₇ : s₇.gpr .r5 = s.gpr .r5 := by
    rw [g₇ _ (by decide) (by decide), g₆ _ (by decide) (by decide) (by decide)]
  have hT₆ : bytesAt s₆.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.tA s₀) H.D = bytesAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.tA s₀) H.D :=
    Memory.frame_bytesAt f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.t_s.sub_right (VG.Proof.Pbkdf2.Md.Arm.Iterate.scr_sub (a := H.blkO) (n := H.N) (by simp only [Hash.blkO]; omega))) (by omega_using [hz_DN, hz_N64])
  refine k s₈ h₈ (by rw [u₈.gpr, x5₇]) (by rw [z₈, x5₇]) ?_ ?_ ?_ ?_
  · rw [u₈.mem]
    refine (f₆.sub fun r hr => ?_).trans (f₇.mono (by simp))
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Proof.Pbkdf2.Md.Arm.Iterate.sub_body (by simp only [Hash.hvO, Hash.blkO]; omega) (by simp only [Hash.hvO, Hash.blkO]; omega_using [hz_NL])
  · rw [u₈.mem]
    exact (Memory.frame_bytesAt f₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.t_s.sub_right (by rw [Memory.add_ofNat]; exact VG.Proof.Pbkdf2.Md.Arm.Iterate.scr_sub (by simp only [Hash.blkO]; omega_using [hz_pad, hp_fits]))).symm)
      (by omega)).trans p₆
  · rw [u₈.mem, m₇, bytesAt_writeBytes_sep _ _ (hd.symm.sep (Region.contains_self _ _) (by
      rw [hxl]; exact Region.contains_self _ _)) (by omega_using [hz_DN, hz_N64]), b₆]
  · rw [u₈.mem, m₇, bytesAt_writeBytes_self' hxl (by omega), hT₆, b₆]

omit hz hp in
theorem iterate_succ (f : List Byte → List Byte) (n : Nat) (u t : List Byte) :
    Spec.Pbkdf2.iterate f (n + 1) u t = Spec.Pbkdf2.iterate f n (f u) (Spec.Pbkdf2.xorBytes t (f u)) := rfl

theorem body_ok {md : Md H.B H.N H.L} (ho : VG.Proof.Pbkdf2.Md.Arm.OutOk md H.out) (hR : md.Reloc) (hf : VG.Proof.Pbkdf2.Md.Arm.CompOk md H.so H.compC)
    {r : Nat} {s : State} (h : VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc md s₀ (r + 1) s) :
    WP isa H.body s fun s' => VG.Arm.eval .ne s' = some (r != 0) ∧ VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc md s₀ r s' := by
  have hz_N64 := hz.N64; have hp_fits := hp.fits; have hz_DN := hz.DN; have hz_pad := hz.pad; have hz_NL := hz.NL; have hz_N4 := hz.N4
  have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  have hB4 : H.B % 4 = 0 := by rcases hz.B with h | h <;> omega
  unfold Hash.body
  refine WP.seq (VG.Proof.Pbkdf2.Md.Arm.Iterate.lc_ok hz hp hR hf (o := 0) (by omega_using []) rfl h.toRegs h.pad fun s₂ h₂ x5₂ f₂ g₂ p₂ _ e₂ => ?_)
  refine WP.seq (VG.Proof.Pbkdf2.Md.Arm.Iterate.digest_ok hz hp ho h₂ p₂ fun s₃ g₃ rd₃ wr₃ sp₃ f₃ b₃ p₃ => ?_)
  have h₃ := h₂.write (fun r hr => g₃ r (VG.Proof.Pbkdf2.Md.Arm.Iterate.ne9 r hr) (VG.Proof.Pbkdf2.Md.Arm.Iterate.ne10 r hr) (VG.Proof.Pbkdf2.Md.Arm.Iterate.ne12 r hr)) rd₃ wr₃ sp₃
    (VG.Proof.Pbkdf2.Md.Arm.Iterate.frame_scr (a := H.blkO) (by simp only [Hash.blkO]; omega_using [hz_NL, hp_fits]) f₃)
  refine VG.Proof.Pbkdf2.Md.Arm.Iterate.lc_ok hz hp hR hf (o := H.N + H.B) (by omega_using []) (by omega) h₃ p₃ fun s₅ h₅ x5₅ f₅ g₅ p₅ _ e₅ => ?_
  refine VG.Proof.Pbkdf2.Md.Arm.Iterate.tail_ok hz hp ho h₅ p₅ fun s₈ h₈ x5₈ z₈ f₈ p₈ b₈ t₈ => ?_
  rw [e₅, b₃, e₂, VG.Proof.Pbkdf2.Md.Arm.Iterate.add0] at b₈ t₈
  have x5₅' : s₅.gpr .r5 = BitVec.ofNat 32 (r + 1) := by
    rw [x5₅, g₃ _ (by decide) (by decide) (by decide), x5₂, h.r5]
  have hlt : r + 1 < 2 ^ 32 := by
    have h_le := h.le; have := (s₀.gpr .r2).isLt; simp only [VG.Proof.Pbkdf2.Md.Arm.Iterate.nn] at *; omega_using [h_le]
  have e₈ : s₅.gpr .r5 - 1 = BitVec.ofNat 32 r := by
    rw [x5₅', show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.add_sub_cancel]
  have fb : Frame (VG.Proof.Pbkdf2.Md.Arm.Iterate.bodyR H s₀) s.mem s₈.mem :=
    ((f₂.trans (f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.Pbkdf2.Md.Arm.Iterate.sub_body (by simp only [Hash.hvO, Hash.blkO]; omega_using []) (by simp only [Hash.hvO, Hash.blkO]; omega_using [hz_NL]))).trans
      f₅).trans f₈
  have hT₅ : bytesAt s₅.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.tA s₀) H.D = bytesAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.tA s₀) H.D := by
    refine Memory.frame_bytesAt (rs := [⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.scA s₀, H.so⟩, ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀, H.N + H.B⟩])
      (((g₂.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)).trans (g₅.sub fun r hr => ?_)) (fun r hr => ?_)
      (by omega_using [hz_DN, hz_N64])
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    · rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀, H.N + H.B⟩, by simp, Region.sub_prefix (by omega_using [])⟩
    · subst hr; exact ⟨⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀, H.N + H.B⟩, by simp, Offset.sub _ (by simp only [Hash.hvO, Hash.blkO]; omega)
        (by simp only [Hash.hvO, Hash.blkO]; omega_using [hz_NL])⟩
    · rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.hvA H s₀, H.N + H.B⟩, by simp, Region.sub_prefix (by omega)⟩
    · have hz_so := hz.so; have hz_W := hz.W
      rcases hr with rfl | rfl
      · exact hp.t_s.sub_right (Region.sub_prefix (by rw [VG.Proof.Pbkdf2.Md.Arm.Iterate.buf_eq H] at *; omega_using [hz_so, hp_fits]))
      · exact hp.t_s.sub_right (VG.Proof.Pbkdf2.Md.Arm.Iterate.scr_sub (by simp only [Hash.hvO]; omega_using [hp_fits]))
  rw [hT₅] at t₈
  refine ⟨?_, h₈, by rw [x5₈, e₈], h.saved.frame H.st fb (VG.Proof.Pbkdf2.Md.Arm.Iterate.saved_disj hz hp), p₈, by have h_le := h.le; omega, ?_⟩
  · simp only [eval_ne, z₈, e₈, ofNat_beq_zero (by omega : r < 2 ^ 32)]
    cases r <;> rfl
  · rw [h.val, VG.Proof.Pbkdf2.Md.Arm.Iterate.iterate_succ, b₈, t₈]; rfl

theorem loop_ok {md : Md H.B H.N H.L} (ho : VG.Proof.Pbkdf2.Md.Arm.OutOk md H.out) (hR : md.Reloc) (hf : VG.Proof.Pbkdf2.Md.Arm.CompOk md H.so H.compC)
    {n : Nat} {s : State} (h : VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc md s₀ n s) (hzf : s.z = decide (n = 0)) :
    WP isa (.ite .eq (.block []) (.loop H.body .ne)) s (VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc md s₀ 0) := by
  refine WP.ite (decide (n = 0)) (by show VG.Arm.eval .eq s = _; rw [eval_eq, hzf]) (fun hb => ?_) (fun hb => ?_)
  · obtain rfl : n = 0 := by simpa using hb
    exact WP.block_nil h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hb; omega⟩
    refine WP.loop (fun m s => VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc md s₀ (m + 1) s)
      (fun m s hs' => WP.mono (VG.Proof.Pbkdf2.Md.Arm.Iterate.body_ok hz hp ho hR hf hs') fun s' ⟨he, hi⟩ => ?_) m s h
    cases m with
    | zero => exact .inl ⟨he, hi⟩
    | succ m => exact .inr ⟨he, m, by omega, hi⟩

end

/-! ## The prologue -/

/-- After saving our caller's registers and our return address and setting
up our registers. -/
structure Setup (H : Hash) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r0 : s.gpr .r0 = VG.Proof.Pbkdf2.Md.Arm.Iterate.hv H s₀
  r1 : s.gpr .r1 = VG.Proof.Pbkdf2.Md.Arm.Iterate.up s₀
  r3 : s.gpr .r3 = VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀
  r4 : s.gpr .r4 = VG.Proof.Pbkdf2.Md.Arm.Iterate.key s₀
  r5 : s.gpr .r5 = s₀.gpr .r2
  r6 : s.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.Iterate.blk H s₀
  r7 : s.gpr .r7 = VG.Proof.Pbkdf2.Md.Arm.Iterate.tp s₀
  r11 : s.gpr .r11 = VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀
  mem : Frame [saveR H.st (VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀)] s₀.mem s.mem
  saved : SavedRegs H.st (VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀) s₀ s.mem

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

section
variable {H : Hash} {sc : Nat} (hz : VG.Proof.Pbkdf2.Md.Arm.Sizes H) {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.Arm.Iterate.Pre H sc s₀)
include hz hp

omit hz in
theorem save_sub : Region.Sub (saveR H.st (VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀)) (VG.Proof.Pbkdf2.Md.Arm.Iterate.scR sc s₀) := by
  have := hp.fits; rw [VG.Proof.Pbkdf2.Md.Arm.Iterate.buf_eq H] at this; exact VG.Proof.Pbkdf2.Md.Arm.Iterate.scr_sub (by omega)

theorem setup_ok {rest : List Instr} {Q : State → Prop} (k : ∀ s, VG.Proof.Pbkdf2.Md.Arm.Iterate.Setup H s₀ s → WP isa (.block rest) s Q) :
    WP isa (.block (([.ldrSp .r12 0] : List Instr) ++ H.st.save ++ ([.mov .r11 (.reg .r12), .mov .r7 (.reg .r3),
      .mov .r3 (.reg .r12), .mov .r4 (.reg .r0), .mov .r5 (.reg .r2)] : List Instr) ++ H.atHv ++ rest)) s₀ Q := by
  have hp_fits := hp.fits; have hp_ns := hp.ns; have hz_W := hz.W; have hz_N64 := hz.N64
  have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  rw [VG.Proof.Pbkdf2.Md.Arm.Iterate.buf_eq H] at *
  simp only [List.append_assoc, List.singleton_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.argR s₀, by simp [hp.rd], Region.contains_self _ _⟩
    fun s₁ u₁ => ?_
  refine Pbkdf2.Stream.Arm.save_ok H.st (scr := VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀) u₁.gpr hz.W (by rw [u₁.wr, hp.wr]; simp) (L := 8 * sc)
    (by omega) hp.ns fun s₂ g₂ rd₂ wr₂ sp₂ f₂ sv₂ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => ?_
  unfold Hash.atHv
  rw [List.append_assoc]
  refine VG.Proof.Pbkdf2.Md.Arm.scrAt_ok (by simp only [Hash.hvO, VG.Proof.Pbkdf2.Md.Arm.Iterate.buf_eq H]; omega) fun s₈ g₈ d₈ m₈ rd₈ wr₈ sp₈ =>
    VG.Proof.Pbkdf2.Md.Arm.scrAt_ok (by simp only [Hash.blkO, VG.Proof.Pbkdf2.Md.Arm.Iterate.buf_eq H]; omega) fun s₉ g₉ d₉ m₉ rd₉ wr₉ sp₉ => k s₉ ?_
  have e₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  have e₇ : ∀ r, r ≠ .r11 → r ≠ .r7 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → s₇.gpr r = s₂.gpr r :=
    fun r h11 h7 h3 h4 h5 => by rw [u₇.other r h5, u₆.other r h4, u₅.other r h3, u₄.other r h7, u₃.other r h11]
  have r11₇ : s₇.gpr .r11 = VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀ := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      g₂, u₁.gpr]; rfl
  have e₉ : ∀ r, r ≠ .r0 → r ≠ .r6 → r ≠ .r12 → s₉.gpr r = s₇.gpr r := fun r h0 h6 h12 => by
    rw [g₉ r h6 h12, g₈ r h0 h12]
  have r11₈ : s₈.gpr .r11 = VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀ := by rw [g₈ _ (by decide) (by decide), r11₇]
  have hm : s₉.mem = s₂.mem := by rw [m₉, m₈, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  exact {
    rd := by rw [rd₉, rd₈, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
    wr := by rw [wr₉, wr₈, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
    sp := by rw [sp₉, sp₈, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
    r0 := by rw [g₉ _ (by decide) (by decide), d₈, r11₇]
    r1 := by rw [e₉ _ (by decide) (by decide) (by decide), e₇ _ (by decide) (by decide) (by decide) (by decide)
      (by decide), e₂ _ (by decide)]
    r3 := by rw [e₉ _ (by decide) (by decide) (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.gpr]; rfl
    r4 := by rw [e₉ _ (by decide) (by decide) (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]
    r5 := by rw [e₉ _ (by decide) (by decide) (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]
    r6 := by rw [d₉, r11₈]
    r7 := by rw [e₉ _ (by decide) (by decide) (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), e₂ _ (by decide)]
    r11 := by rw [e₉ _ (by decide) (by decide) (by decide), r11₇]
    mem := by rw [hm]; rw [← u₁.mem]; exact f₂
    saved := by
      rw [hm]
      exact sv₂.of_eq H.st fun r hr => u₁.other r (by
        simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) }

/-- Writing `U`, the padding and the length field into the block. -/
theorem fill_ok {md : Md H.B H.N H.L}
    (hlen : VG.Proof.Pbkdf2.Md.Arm.wordsBytes (lenWords H.be H.L (H.B + H.D)) = md.lenBytes (H.B + H.D)) {s : State} (h : VG.Proof.Pbkdf2.Md.Arm.Iterate.Setup H s₀ s) :
    WP isa (.block (copyW .r1 .r6 0 0 (H.D / 4) ++ H.pad ++ ([.cmp .r5 (.imm 0)] : List Instr))) s
      fun s' => VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc md s₀ (VG.Proof.Pbkdf2.Md.Arm.Iterate.nn s₀) s' ∧ s'.z = decide (VG.Proof.Pbkdf2.Md.Arm.Iterate.nn s₀ = 0) := by
  have hz_N64 := hz.N64; have hp_fits := hp.fits; have hz_DN := hz.DN; have hz_pad := hz.pad; have hz_NL := hz.NL; have hz_D4 := hz.D4; have hz_L4 := hz.L4
  have hz_L16 := hz.L16; have hp_ns := hp.ns; have hp_nu := hp.nu; have hz_W := hz.W
  have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  have hB4 : H.B % 4 = 0 := by rcases hz.B with h | h <;> omega_using [h]
  have hD4 : 4 * (H.D / 4) = H.D := by omega
  have ablk := VG.Proof.Pbkdf2.Md.Arm.Iterate.addr_blk hz hp
  have tb : (VG.Proof.Pbkdf2.Md.Arm.Iterate.blk H s₀).toNat = (VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀).toNat + H.blkO := VG.Proof.Pbkdf2.Md.Arm.Iterate.toNat_sO hp (by simp only [Hash.blkO]; omega)
  have hbl : ∀ {a n : Nat}, a + n ≤ H.B → H.blkO + a + n ≤ 8 * sc := fun h' => by simp only [Hash.blkO]; omega_using [h', hp_fits]
  unfold Hash.pad
  simp only [List.append_assoc]
  refine VG.Proof.Pbkdf2.Md.Arm.copyW_ok (by decide) (by decide) 0 0 (H.D / 4) ⟨by omega_using [hz_DN, hz_N64], by omega⟩ _ s _
    (by rw [h.r1]; omega_using [hp_nu]) (by rw [h.r6, tb]; simp only [Hash.blkO]; omega_using [hp_ns, hz_pad, hp_fits])
    (fun j hj => ?_) (fun j hj => ?_) ?_ fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  · rw [h.r1, h.rd, hp.rd, VG.Proof.Pbkdf2.Md.Arm.Iterate.add0]
    exact ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.uR H s₀, by simp, Offset.contains_base _ (by omega) (by omega_using [hj, hz_DN, hz_N64])⟩
  · rw [h.r6, ablk, VG.Proof.Pbkdf2.Md.Arm.Iterate.add0]; exact VG.Proof.Pbkdf2.Md.Arm.Iterate.in_blk hp h.wr (by omega_using [hj, hz_pad])
  · rw [h.r1, h.r6, ablk, VG.Proof.Pbkdf2.Md.Arm.Iterate.add0, VG.Proof.Pbkdf2.Md.Arm.Iterate.add0, hD4]
    exact hp.u_s.sep (Region.contains_self _ _)
      (Offset.contains_base _ (by simp only [Hash.blkO]; omega_using [hz_pad, hp_fits]) (by simp only [Hash.blkO]; omega_using [hp_ns, hp_fits]))
  rw [h.r6, ablk, h.r1, VG.Proof.Pbkdf2.Md.Arm.Iterate.add0, VG.Proof.Pbkdf2.Md.Arm.Iterate.add0, hD4] at m₁
  have g6 : s₁.gpr .r6 = VG.Proof.Pbkdf2.Md.Arm.Iterate.blk H s₀ := by rw [g₁ _ (by decide), h.r6]
  refine VG.Proof.Pbkdf2.Md.Arm.padFrom_ok (a := H.D) (b := H.B - H.L) (by omega) (by omega) (by omega_using [hB]) (s := s₁) (p := VG.Proof.Pbkdf2.Md.Arm.Iterate.blk H s₀) g6
    (by rw [tb]; simp only [Hash.blkO]; omega_using [hp_ns, hp_fits]) (fun j hj => by rw [ablk]; exact VG.Proof.Pbkdf2.Md.Arm.Iterate.in_blk hp (wr₁.trans h.wr) (by omega_using [hj]))
    fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  rw [ablk] at m₂
  have lw := HashOK.lenWords_length (H := H)
  refine VG.Proof.Pbkdf2.Md.Arm.constW_ok (p := VG.Proof.Pbkdf2.Md.Arm.Iterate.blk H s₀) (lenWords H.be H.L (H.B + H.D)) (H.B - H.L) (by rw [lw]; omega_using [hB, hz_pad])
    (by rw [lw, tb]; simp only [Hash.blkO]; omega_using [hp_ns, hz_pad, hp_fits]) _ s₂ _ (by rw [g₂ _ (by decide), g6])
    (fun j hj => by rw [lw] at hj; rw [ablk]; exact VG.Proof.Pbkdf2.Md.Arm.Iterate.in_blk hp (wr₂.trans (wr₁.trans h.wr)) (by omega_using [hj, hz_pad]))
    fun s₃ g₃ rd₃ wr₃ sp₃ m₃ => ?_
  rw [ablk, hlen] at m₃
  refine wp_cmp (op2_imm (by decide)) fun s₄ u₄ z₄ => WP.block_nil ?_
  have lpz : ([0x80] ++ List.replicate (H.B - H.L - H.D - 1) 0 : List Byte).length = H.B - H.L - H.D := by
    simp; omega_using [hz_pad]
  have hM : s₄.mem = VG.WriteBytes.writeBytes (VG.WriteBytes.writeBytes (VG.WriteBytes.writeBytes s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀) (bytesAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.uA s₀) H.D))
      (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 H.D) ([0x80] ++ List.replicate (H.B - H.L - H.D - 1) 0))
      (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 (H.B - H.L)) (md.lenBytes (H.B + H.D)) := by
    rw [u₄.mem, m₃, m₂, m₁, show H.B - H.L - H.D - 1 = H.B - H.L - H.D - 1 from rfl]
  have hG : ∀ r, r ≠ .r12 → s₄.gpr r = s.gpr r := fun r hr => by
    rw [u₄.gpr, g₃ r hr, g₂ r hr, g₁ r hr]
  have sbB : Region.Sub ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀, H.B⟩ (VG.Proof.Pbkdf2.Md.Arm.Iterate.scR sc s₀) := VG.Proof.Pbkdf2.Md.Arm.Iterate.scr_sub (by have := hbl (a := 0) (n := H.B) (by omega); omega)
  have fM : Frame [⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀, H.B⟩] s.mem s₄.mem := by
    rw [hM]
    refine ((VG.WriteBytes.writeBytes_frame _ _ _ ?_).trans (VG.WriteBytes.writeBytes_frame _ _ _ ?_)).trans (VG.WriteBytes.writeBytes_frame _ _ _ ?_)
    · rw [bytesAt_length]
      have := Offset.contains_base (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀) (d := 0) (n := H.D) (k := H.B) (by omega_using [hz_pad]) (by omega)
      rwa [VG.Proof.Pbkdf2.Md.Arm.Iterate.add0] at this
    · rw [lpz]; exact Offset.contains_base _ (by omega_using [hz_pad]) (by omega_using [hz_DN, hz_N64])
    · rw [md.lenBytes_length]; exact Offset.contains_base _ (by omega_using [hz_pad]) (by omega_using [hp_ns, hp_fits])
  have S1 : Mem.Sep (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀) H.D (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.L - H.D) := by
    have := Offset.sep (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀) (d := 0) (n := H.D) (e := H.D) (k := H.B - H.L - H.D) (.inl (by omega))
      (by omega_using [hz_DN, hz_N64]) (by omega_using [hp_ns, hz_DN, hp_fits])
    rwa [VG.Proof.Pbkdf2.Md.Arm.Iterate.add0] at this
  have S2 : ∀ {a n : Nat}, a + n ≤ H.B - H.L →
      Mem.Sep (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 a) n (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 (H.B - H.L)) H.L :=
    fun h' => Offset.sep _ (.inl h') (by omega_using [h', hp_ns, hp_fits]) (by omega_using [hp_ns, hz_pad, hp_fits])
  have fS : Frame [VG.Proof.Pbkdf2.Md.Arm.Iterate.tR H s₀, VG.Proof.Pbkdf2.Md.Arm.Iterate.scR sc s₀] s₀.mem s.mem :=
    h.mem.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.scR sc s₀, by simp, VG.Proof.Pbkdf2.Md.Arm.Iterate.save_sub hp⟩
  have hU : bytesAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.uA s₀) H.D = bytesAt s₀.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.uA s₀) H.D :=
    Memory.frame_bytesAt h.mem (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.u_s.sub_right (VG.Proof.Pbkdf2.Md.Arm.Iterate.save_sub hp)) (by omega_using [hz_DN, hz_N64])
  have hT : bytesAt s₄.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.tA s₀) H.D = bytesAt s₀.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.tA s₀) H.D := by
    refine (Memory.frame_bytesAt fM (fun r hr => ?_) (by omega)).trans
      (Memory.frame_bytesAt h.mem (fun r hr => ?_) (by omega))
    · simp only [List.mem_singleton] at hr; subst hr; exact hp.t_s.sub_right sbB
    · simp only [List.mem_singleton] at hr; subst hr; exact hp.t_s.sub_right (VG.Proof.Pbkdf2.Md.Arm.Iterate.save_sub hp)
  refine ⟨⟨⟨by rw [u₄.rd, rd₃, rd₂, rd₁, h.rd], by rw [u₄.wr, wr₃, wr₂, wr₁, h.wr],
    by rw [u₄.sp, sp₃, sp₂, sp₁, h.sp], by rw [hG _ (by decide), h.r0], by rw [hG _ (by decide), h.r3],
    by rw [hG _ (by decide), h.r4], by rw [hG _ (by decide), h.r6], by rw [hG _ (by decide), h.r7],
    by rw [hG _ (by decide), h.r11], fS.trans (fM.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.scR sc s₀, by simp, sbB⟩)⟩,
    by rw [hG _ (by decide), h.r5, VG.Proof.Pbkdf2.Md.Arm.Iterate.ofNat_toNat32],
    h.saved.frame H.st fM (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have hz_W := hz.W; have hp_fits := hp.fits; rw [VG.Proof.Pbkdf2.Md.Arm.Iterate.buf_eq H] at *
      exact Offset.disjoint _ (.inl (by simp only [Hash.blkO, VG.Proof.Pbkdf2.Md.Arm.Iterate.buf_eq H]; omega_using [])) (by omega)
        (by simp only [Hash.blkO, VG.Proof.Pbkdf2.Md.Arm.Iterate.buf_eq H]; omega_using [hz_W, hB, hz_N64])), ?_, Nat.le_refl _, ?_⟩, ?_⟩
  · -- The padding and the length field.
    rw [show H.B - H.D = (H.B - H.L - H.D) + H.L by omega_using [hz_pad], bytesAt_add, Memory.add_ofNat (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀),
      show H.D + (H.B - H.L - H.D) = H.B - H.L by omega_using [hz_pad], hM,
      bytesAt_writeBytes_self' (md.lenBytes_length _) (by omega_using [hz_L16]),
      bytesAt_writeBytes_sep _ _ (by rw [md.lenBytes_length]; exact S2 (by omega_using [hz_pad])) (by omega_using [hp_ns, hp_fits]),
      bytesAt_writeBytes_self' lpz (by omega), Md.tailPad, show H.B - H.L - 1 - H.D = H.B - H.L - H.D - 1 by omega_using []]
  · -- `U` and `T`.
    have hB' : bytesAt s₄.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀) H.D = bytesAt s₀.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.uA s₀) H.D := by
      rw [hM, bytesAt_writeBytes_sep _ _ (by
          rw [md.lenBytes_length]; have := S2 (a := 0) (n := H.D) (by omega_using [hz_pad]); rwa [VG.Proof.Pbkdf2.Md.Arm.Iterate.add0] at this) (by omega),
        bytesAt_writeBytes_sep _ _ (by rw [lpz]; exact S1) (by omega),
        bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega), hU]
    rw [hB', hT]
  · have c := MdStream.Arm.cmp0 (s₀.gpr .r2).isLt
    rw [VG.Proof.Pbkdf2.Md.Arm.Iterate.ofNat_toNat32] at c
    rw [z₄, g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), h.r5, c]

theorem prologue_ok {md : Md H.B H.N H.L}
    (hlen : VG.Proof.Pbkdf2.Md.Arm.wordsBytes (lenWords H.be H.L (H.B + H.D)) = md.lenBytes (H.B + H.D)) :
    WP isa (.block H.prologue) s₀ fun s' => VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc md s₀ (VG.Proof.Pbkdf2.Md.Arm.Iterate.nn s₀) s' ∧ s'.z = decide (VG.Proof.Pbkdf2.Md.Arm.Iterate.nn s₀ = 0) := by
  have := VG.Proof.Pbkdf2.Md.Arm.Iterate.setup_ok hz hp (rest := copyW .r1 .r6 0 0 (H.D / 4) ++ H.pad ++ [.cmp .r5 (.imm 0)])
    fun s h => VG.Proof.Pbkdf2.Md.Arm.Iterate.fill_ok hz hp hlen h
  unfold Hash.prologue
  simpa only [List.append_assoc] using this


theorem epilogue_ok {md : Md H.B H.N H.L} {S : Spec.Hmac.StreamingHash} {iv : md.HV} (hl : md.Link S iv H.D)
    {s : State} (h : VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc md s₀ 0 s) :
    WP isa (.block H.st.restore) s fun s' => abiPreserved s₀ s' ∧ (iterG S sc).post s₀ s' := by
  have hf := hp.fits; have hz_W := hz.W; rw [VG.Proof.Pbkdf2.Md.Arm.Iterate.buf_eq H] at hf
  refine WP.mono (Pbkdf2.Stream.Arm.restore_ok H.st h.r11 hz.W h.saved (by rw [h.wr, hp.wr]; simp) (L := 8 * sc)
    (by omega) hp.ns) fun s' ⟨hm, _, _, hsp, hg, _⟩ =>
      ⟨⟨fun r hr => hg r (preserved_saved r hr), by rw [hsp, h.sp]⟩, fun k0 hk hi ho => ?_⟩
  have hT := h.val
  simp only [Spec.Pbkdf2.iterate] at hT
  rw [hl.hS] at ho
  show bytesAt s'.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.tA s₀) S.digestBytes = _
  rw [hl.hD, hm, ← hT, Md.iterate_hmac hl hk hi ho _ (bytesAt_length _ _ _)]

end

/-! ## Correctness -/

theorem correct {H : Hash} (hH : VG.Proof.Pbkdf2.Md.Arm.HashOK H) {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.Arm.Iterate.Pre H sc s₀) :
    WP isa H.iterate s₀ fun s' => abiPreserved s₀ s' ∧ (iterG hH.SH sc).post s₀ s' := by
  unfold Hash.iterate
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.Arm.Iterate.prologue_ok hH.sizes hp hH.len) fun s₁ ⟨h₁, z₁⟩ => ?_)
  exact WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.Arm.Iterate.loop_ok hH.sizes hp hH.out hH.reloc hH.comp h₁ z₁) fun s₂ h₂ =>
    VG.Proof.Pbkdf2.Md.Arm.Iterate.epilogue_ok hH.sizes hp hH.link h₂)

end VG.Proof.Pbkdf2.Md.Arm.Iterate

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.Arm.IterateCT`. -/
section

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on ARMv7: constant time

As on AArch64 (`Proof/Pbkdf2/AArch64/IterateCT.lean`): this holds for any
compression function (`CompOk`), so it is proven once. The taint analysis
cannot prove it without looking into the compression function (it would lose
our registers, which the compression function saves and restores in a scratch
space it also stores secrets into through a register that is not the base of a
region), so we relate two runs (`RelCT`): at every point, correctness
determines our registers from the public arguments alone, so they agree;
between the calls, the taint analysis proves each block constant time from
that (`Checks`, evaluated for each hash function, since the code depends on
its sizes); and the calls are constant time by the compression function's own
proof (`compressBlock_rel`).
-/

namespace VG.Proof.Pbkdf2.Md.Arm.Iterate

open VG VG.Arm
open VG.Impl.Pbkdf2.Md.Arm (Hash xorW)
open VG.Proof.Pbkdf2.Md.Arm
open VG.Proof.MdStream (Md)
open VG.Proof.MdStream.Arm (wp_mov op2_reg eval_eq eval_ne)
open VG.Proof.Pbkdf2.Stream.Arm (iterG)
open VG.Spec.Sha256 (bytesAt)

/-- The registers the blocks between the calls use. -/
abbrev regsS : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r11]

/-- The taint checks of the pieces of `iterate` between its calls, which
depend on the hash function's sizes, its length field and its digest. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (taint.check (argTaint [.r0, .r1, .r2, .r3] 4) (.block H.prologue) hc).isSome = true
  load : ∃ hc, (taint.check (Taint.ofRegs VG.Proof.Pbkdf2.Md.Arm.Iterate.regsS) (.block (H.loadKey 0)) hc).isSome = true
  mid : ∃ hc, (taint.check (Taint.ofRegs VG.Proof.Pbkdf2.Md.Arm.Iterate.regsS) (.block (H.digest ++ H.loadKey (H.N + H.B))) hc).isSome = true
  fin : ∃ hc, (taint.check (Taint.ofRegs VG.Proof.Pbkdf2.Md.Arm.Iterate.regsS) (.block (H.digest ++ (List.range (H.D / 4)).flatMap xorW ++
    [.subs .r5 .r5 (.imm 1)])) hc).isSome = true
  epi : ∃ hc, (taint.check (Taint.ofRegs [.r11]) (.block H.st.restore) hc).isSome = true
  ite : ∃ hc, (taint.check (Taint.ofRegs []) (.block []) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  r0 : s₀.gpr .r0 = s₀'.gpr .r0
  r1 : s₀.gpr .r1 = s₀'.gpr .r1
  r2 : s₀.gpr .r2 = s₀'.gpr .r2
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  a0 : stackArg s₀ 0 = stackArg s₀' 0

theorem PubEq.nn {s₀ s₀' : State} (hq : VG.Proof.Pbkdf2.Md.Arm.Iterate.PubEq s₀ s₀') : VG.Proof.Pbkdf2.Md.Arm.Iterate.nn s₀ = VG.Proof.Pbkdf2.Md.Arm.Iterate.nn s₀' := congrArg BitVec.toNat hq.r2

/-- The state during a step, with `v` in `r5`. -/
structure St (H : Hash) (sc : Nat) (md : Md H.B H.N H.L) (s₀ : State) (v : BitVec 32) (s : State) : Prop
    extends VG.Proof.Pbkdf2.Md.Arm.Iterate.Regs H sc s₀ s where
  r5 : s.gpr .r5 = v
  pad : bytesAt s.mem (VG.Proof.Pbkdf2.Md.Arm.Iterate.blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.D) = md.tailPad H.D

section
variable {H : Hash} {sc : Nat} {md : Md H.B H.N H.L}

/-- The registers the blocks use agree in two runs. -/
theorem St.agree {s₀ s₀' : State} (hq : VG.Proof.Pbkdf2.Md.Arm.Iterate.PubEq s₀ s₀') {v : BitVec 32} {s s' : State} (h : VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀ v s)
    (h' : VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀' v s') : ∀ r ∈ VG.Proof.Pbkdf2.Md.Arm.Iterate.regsS, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.r0, h'.r0, VG.Proof.Pbkdf2.Md.Arm.Iterate.hv, VG.Proof.Pbkdf2.Md.Arm.Iterate.hv, VG.Proof.Pbkdf2.Md.Arm.Iterate.scr, VG.Proof.Pbkdf2.Md.Arm.Iterate.scr, hq.a0]
  · rw [h.r3, h'.r3, VG.Proof.Pbkdf2.Md.Arm.Iterate.scr, VG.Proof.Pbkdf2.Md.Arm.Iterate.scr, hq.a0]
  · rw [h.r4, h'.r4, VG.Proof.Pbkdf2.Md.Arm.Iterate.key, VG.Proof.Pbkdf2.Md.Arm.Iterate.key, hq.r0]
  · rw [h.r5, h'.r5]
  · rw [h.r6, h'.r6, VG.Proof.Pbkdf2.Md.Arm.Iterate.blk, VG.Proof.Pbkdf2.Md.Arm.Iterate.blk, VG.Proof.Pbkdf2.Md.Arm.Iterate.scr, VG.Proof.Pbkdf2.Md.Arm.Iterate.scr, hq.a0]
  · rw [h.r7, h'.r7, VG.Proof.Pbkdf2.Md.Arm.Iterate.tp, VG.Proof.Pbkdf2.Md.Arm.Iterate.tp, hq.r3]
  · rw [h.r11, h'.r11, VG.Proof.Pbkdf2.Md.Arm.Iterate.scr, VG.Proof.Pbkdf2.Md.Arm.Iterate.scr, hq.a0]

theorem St.of_inv {s₀ : State} {r : Nat} {s : State} (h : VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc md s₀ (r + 1) s) :
    VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀ (BitVec.ofNat 32 (r + 1)) s :=
  ⟨h.toRegs, h.r5, h.pad⟩

variable (hz : VG.Proof.Pbkdf2.Md.Arm.Sizes H) {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.Arm.Iterate.Pre H sc s₀) {v : BitVec 32}
include hz hp

/-! ## What each piece of a step does, in one run -/

theorem load_st (hR : md.Reloc) {o : Nat} (ho : o + H.N ≤ 2 * (H.N + H.B)) (ho4 : o % 4 = 0) {s : State}
    (h : VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀ v s) :
    WP isa (.block (H.loadKey o)) s (VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀ v) := by
  have := hz.N64; have := hp.fits; have := hz.DN; have := hz.pad; have := hz.NL
  have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  rw [← List.append_nil (H.loadKey o)]
  exact VG.Proof.Pbkdf2.Md.Arm.Iterate.load_ok hz hp hR h.toRegs ho ho4 fun s' g rd wr sp f _ => WP.block_nil
    ⟨h.toRegs.write (fun r hr => g r (VG.Proof.Pbkdf2.Md.Arm.Iterate.ne12 r hr)) rd wr sp (VG.Proof.Pbkdf2.Md.Arm.Iterate.frame_scr (a := H.hvO) (by simp only [Hash.hvO]; omega) f),
      (g _ (by decide)).trans h.r5,
      (Memory.frame_bytesAt f (fun r hr => VG.Proof.Pbkdf2.Md.Arm.Iterate.blk_disj hz hp (by omega) r (by simp at hr; simp [hr])) (by omega)).trans
        h.pad⟩

theorem cmp_st (hf : VG.Proof.Pbkdf2.Md.Arm.CompOk md H.so H.compC) {s : State} (h : VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀ v s) :
    WP isa H.compressBlock s (VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀ v) := by
  have := hz.N64; have := hp.fits; have := hz.DN; have := hz.pad; have := hz.NL
  have : H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  exact VG.Proof.Pbkdf2.Md.Arm.Iterate.cmp_ok hz hp hf h.toRegs fun s' h' x5 f _ =>
    ⟨h', x5.trans h.r5, (Memory.frame_bytesAt f (VG.Proof.Pbkdf2.Md.Arm.Iterate.blk_disj hz hp (by omega)) (by omega)).trans h.pad⟩

theorem mid_st (ho : VG.Proof.Pbkdf2.Md.Arm.OutOk md H.out) (hR : md.Reloc) {s : State} (h : VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀ v s) :
    WP isa (.block (H.digest ++ H.loadKey (H.N + H.B))) s (VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀ v) := by
  have := hz.N64; have := hp.fits; have := hz.NL; have := hz.N4
  have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  have hB4 : H.B % 4 = 0 := by rcases hz.B with h | h <;> omega
  refine VG.Proof.Pbkdf2.Md.Arm.Iterate.digest_ok hz hp ho h.toRegs h.pad fun s' g rd wr sp f _ p => ?_
  exact VG.Proof.Pbkdf2.Md.Arm.Iterate.load_st hz hp hR (by omega) (by omega)
    ⟨h.toRegs.write (fun r hr => g r (VG.Proof.Pbkdf2.Md.Arm.Iterate.ne9 r hr) (VG.Proof.Pbkdf2.Md.Arm.Iterate.ne10 r hr) (VG.Proof.Pbkdf2.Md.Arm.Iterate.ne12 r hr)) rd wr sp
      (VG.Proof.Pbkdf2.Md.Arm.Iterate.frame_scr (a := H.blkO) (by simp only [Hash.blkO]; omega) f),
      (g _ (by decide) (by decide) (by decide)).trans h.r5, p⟩

/-! ## Two runs -/

variable {s₀' : State} (hp' : VG.Proof.Pbkdf2.Md.Arm.Iterate.Pre H sc s₀') (hq : VG.Proof.Pbkdf2.Md.Arm.Iterate.PubEq s₀ s₀')
include hp' hq

theorem cmp_rel (hf : VG.Proof.Pbkdf2.Md.Arm.CompOk md H.so H.compC) :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀ v s ∧ VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀' v s') H.compressBlock fun s s' =>
      VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀ v s ∧ VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀' v s' := by
  have e : VG.Proof.Pbkdf2.Md.Arm.Iterate.hv H s₀' = VG.Proof.Pbkdf2.Md.Arm.Iterate.hv H s₀ ∧ VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀' = VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀ ∧ VG.Proof.Pbkdf2.Md.Arm.Iterate.blk H s₀' = VG.Proof.Pbkdf2.Md.Arm.Iterate.blk H s₀ := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [VG.Proof.Pbkdf2.Md.Arm.Iterate.hv, VG.Proof.Pbkdf2.Md.Arm.Iterate.blk, VG.Proof.Pbkdf2.Md.Arm.Iterate.scr, hq.a0]
  have call := VG.Proof.Pbkdf2.Md.Arm.compressBlock_rel (H := md) (so := H.so) hf (name := H.compN) (st := VG.Proof.Pbkdf2.Md.Arm.Iterate.hv H s₀) (scr := VG.Proof.Pbkdf2.Md.Arm.Iterate.scr s₀)
    (src := VG.Proof.Pbkdf2.Md.Arm.Iterate.blk H s₀) (P' := fun s s' => VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀ v s ∧ VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀' v s')
    fun s s' ⟨h, h'⟩ => by
      have c' := VG.Proof.Pbkdf2.Md.Arm.Iterate.callOk_of hz hp' h'.toRegs
      rw [e.1, e.2.1, e.2.2] at c'
      exact ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.callOk_of hz hp h.toRegs, c'⟩
  exact (call.wp fun _ _ h => ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.cmp_st hz hp hf h.1, VG.Proof.Pbkdf2.Md.Arm.Iterate.cmp_st hz hp' hf h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

omit hz in
/-- A block the taint analysis checks from `regsS`. -/
theorem blk_rel {c : Prog isa} {G : State → State → Prop}
    (hc : ∃ hc, (taint.check (Taint.ofRegs VG.Proof.Pbkdf2.Md.Arm.Iterate.regsS) c hc).isSome = true)
    (hw : ∀ {t₀ : State}, VG.Proof.Pbkdf2.Md.Arm.Iterate.Pre H sc t₀ → ∀ s, VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md t₀ v s → WP isa c s (G t₀)) :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀ v s ∧ VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀' v s') c fun s s' => G s₀ s ∧ G s₀' s' := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Pbkdf2.Md.Arm.Iterate.regsS) (fun _ _ h =>
    Taint.agree_ofRegs (St.agree hq h.1 h.2)) hc).wp fun _ _ h => ⟨hw hp _ h.1, hw hp' _ h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem body_rel (ho : VG.Proof.Pbkdf2.Md.Arm.OutOk md H.out) (hR : md.Reloc) (hf : VG.Proof.Pbkdf2.Md.Arm.CompOk md H.so H.compC) (hc : VG.Proof.Pbkdf2.Md.Arm.Iterate.Checks H) {r : Nat} :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc md s₀ (r + 1) s ∧ VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc md s₀' (r + 1) s') H.body
      fun s s' => (VG.Arm.eval .ne s = some (r != 0) ∧ VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc md s₀ r s) ∧
        (VG.Arm.eval .ne s' = some (r != 0) ∧ VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc md s₀' r s') := by
  have := hz.N64; have := hz.NL
  have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  have l0 : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀ (BitVec.ofNat 32 (r + 1)) s ∧
      VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀' (BitVec.ofNat 32 (r + 1)) s') (.block (H.loadKey 0))
      fun s s' => VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀ (BitVec.ofNat 32 (r + 1)) s ∧ VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀' (BitVec.ofNat 32 (r + 1)) s' :=
    VG.Proof.Pbkdf2.Md.Arm.Iterate.blk_rel hp hp' hq (G := fun t₀ => VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md t₀ (BitVec.ofNat 32 (r + 1))) hc.load
      fun hp _ h => VG.Proof.Pbkdf2.Md.Arm.Iterate.load_st hz hp hR (by omega) rfl h
  have dl : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀ (BitVec.ofNat 32 (r + 1)) s ∧
      VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀' (BitVec.ofNat 32 (r + 1)) s') (.block (H.digest ++ H.loadKey (H.N + H.B)))
      fun s s' => VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀ (BitVec.ofNat 32 (r + 1)) s ∧ VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀' (BitVec.ofNat 32 (r + 1)) s' :=
    VG.Proof.Pbkdf2.Md.Arm.Iterate.blk_rel hp hp' hq (G := fun t₀ => VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md t₀ (BitVec.ofNat 32 (r + 1))) hc.mid
      fun hp _ h => VG.Proof.Pbkdf2.Md.Arm.Iterate.mid_st hz hp ho hR h
  obtain ⟨_, hfi⟩ := hc.fin
  have fin : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀ (BitVec.ofNat 32 (r + 1)) s ∧
      VG.Proof.Pbkdf2.Md.Arm.Iterate.St H sc md s₀' (BitVec.ofNat 32 (r + 1)) s')
      (.block (H.digest ++ (List.range (H.D / 4)).flatMap xorW ++ [.subs .r5 .r5 (.imm 1)])) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Pbkdf2.Md.Arm.Iterate.regsS) (fun _ _ h => Taint.agree_ofRegs (St.agree hq h.1 h.2)) hfi
  have c := VG.Proof.Pbkdf2.Md.Arm.Iterate.cmp_rel hz hp hp' hq (v := BitVec.ofNat 32 (r + 1)) hf
  have hb : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc md s₀ (r + 1) s ∧ VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc md s₀' (r + 1) s') H.body fun _ _ => True :=
    fun s s' t t' u u' h e e' => by
      unfold Hash.body at e e'
      exact (l0.seq (c.seq (dl.seq (c.seq fin)))) s s' t t' u u' ⟨St.of_inv h.1, St.of_inv h.2⟩ e e'
  exact (hb.wp fun _ _ h => ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.body_ok hz hp ho hR hf h.1, VG.Proof.Pbkdf2.Md.Arm.Iterate.body_ok hz hp' ho hR hf h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem loop_rel (ho : VG.Proof.Pbkdf2.Md.Arm.OutOk md H.out) (hR : md.Reloc) (hf : VG.Proof.Pbkdf2.Md.Arm.CompOk md H.so H.compC) (hc : VG.Proof.Pbkdf2.Md.Arm.Iterate.Checks H) {n : Nat} :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc md s₀ (n + 1) s ∧ VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc md s₀' (n + 1) s') (.loop H.body .ne)
      fun _ _ => True :=
  RelCT.loop (M := isa) (body := H.body) (c := .ne) (Q := fun _ _ => True)
    (fun m s s' => VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc md s₀ (m + 1) s ∧ VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc md s₀' (m + 1) s') (fun m => by
      intro s s' t t' u u' h e e'
      obtain ⟨ht, ⟨z, i⟩, ⟨z', i'⟩⟩ := VG.Proof.Pbkdf2.Md.Arm.Iterate.body_rel hz hp hp' hq ho hR hf hc _ _ _ _ _ _ h e e'
      refine ⟨ht, z.trans z'.symm, fun _ => trivial, fun hc' => ?_⟩
      have hc'' : some (m != 0) = some true := z.symm.trans hc'
      cases m with
      | zero => cases hc''
      | succ m => exact ⟨m, by omega, i, i'⟩) n

end

theorem iterate_rel {H : Hash} (hH : VG.Proof.Pbkdf2.Md.Arm.HashOK H) (hc : VG.Proof.Pbkdf2.Md.Arm.Iterate.Checks H) {sc : Nat} {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Md.Arm.Iterate.Pre H sc s₀)
    (hp' : VG.Proof.Pbkdf2.Md.Arm.Iterate.Pre H sc s₀') (hq : VG.Proof.Pbkdf2.Md.Arm.Iterate.PubEq s₀ s₀') :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.iterate fun _ _ => True := by
  have hz := hH.sizes
  obtain ⟨_, hpr⟩ := hc.pro
  obtain ⟨_, hep⟩ := hc.epi
  obtain ⟨_, hit⟩ := hc.ite
  have hlt : ∀ {s₀ : State}, VG.Proof.Pbkdf2.Md.Arm.Iterate.nn s₀ < 2 ^ 32 := fun {s₀} => (s₀.gpr .r2).isLt
  have aw : ∀ {t : State}, VG.Proof.Pbkdf2.Md.Arm.Iterate.Pre H sc t →
      t.sp.toNat + 4 ≤ 2 ^ 32 ∧ ∀ r ∈ t.wr, Region.Disjoint ⟨State.addr t.sp, 4⟩ r := fun {t} h => by
    have e : (⟨State.addr t.sp, 4⟩ : Region) = VG.Proof.Pbkdf2.Md.Arm.Iterate.argR t := by simp [stackArgAddr]
    refine ⟨h.spf, ?_⟩
    simp only [e, h.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact h.a_t
    · exact h.a_s
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.prologue) fun s s' =>
      (VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc hH.md s₀ (VG.Proof.Pbkdf2.Md.Arm.Iterate.nn s₀) s ∧ s.z = decide (VG.Proof.Pbkdf2.Md.Arm.Iterate.nn s₀ = 0)) ∧
        (VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc hH.md s₀' (VG.Proof.Pbkdf2.Md.Arm.Iterate.nn s₀') s' ∧ s'.z = decide (VG.Proof.Pbkdf2.Md.Arm.Iterate.nn s₀' = 0)) :=
    rel_agree (argTaint [.r0, .r1, .r2, .r3] 4) (fun s s' e e' => by
        rw [e, e']
        refine agree_argTaint (fun r hr => ?_) hq.sp (aw hp) (aw hp')
          (argMem_of (j := 1) hq.sp hp.spf fun i hi => by rw [show i = 0 by omega]; exact hq.a0)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.r0
        · exact hq.r1
        · exact hq.r2
        · exact hq.r3) ⟨_, hpr⟩
      (fun _ e => by rw [e]; exact VG.Proof.Pbkdf2.Md.Arm.Iterate.prologue_ok hz hp hH.len)
      (fun _ e => by rw [e]; exact VG.Proof.Pbkdf2.Md.Arm.Iterate.prologue_ok hz hp' hH.len)
  have br : RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc hH.md s₀ (VG.Proof.Pbkdf2.Md.Arm.Iterate.nn s₀) s ∧ s.z = decide (VG.Proof.Pbkdf2.Md.Arm.Iterate.nn s₀ = 0)) ∧
        (VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc hH.md s₀' (VG.Proof.Pbkdf2.Md.Arm.Iterate.nn s₀') s' ∧ s'.z = decide (VG.Proof.Pbkdf2.Md.Arm.Iterate.nn s₀' = 0)))
      (.ite .eq (.block []) (.loop H.body .ne))
      fun s s' => VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc hH.md s₀ 0 s ∧ VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc hH.md s₀' 0 s' := by
    refine (RelCT.ite (fun s s' h => ?_) (RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ _ => Taint.agree_ofRegs (by simp)) hit) ?_).wp
      (fun _ _ h => ⟨VG.Proof.Pbkdf2.Md.Arm.Iterate.loop_ok hz hp hH.out hH.reloc hH.comp h.1.1 h.1.2,
        VG.Proof.Pbkdf2.Md.Arm.Iterate.loop_ok hz hp' hH.out hH.reloc hH.comp h.2.1 h.2.2⟩)
      |>.mono (fun _ _ h => h) fun _ _ h => h.2
    · show VG.Arm.eval .eq s = VG.Arm.eval .eq s'
      rw [eval_eq, eval_eq, h.1.2, h.2.2, hq.nn]
    · intro s s' t t' u u' ⟨⟨⟨i, zi⟩, ⟨i', _⟩⟩, hc'⟩ e e'
      have hc'' : some (decide (VG.Proof.Pbkdf2.Md.Arm.Iterate.nn s₀ = 0)) = some false := by rw [← zi, ← eval_eq]; exact hc'
      have hne : VG.Proof.Pbkdf2.Md.Arm.Iterate.nn s₀ ≠ 0 := fun h0 => by rw [h0] at hc''; cases hc''
      obtain ⟨m, hm⟩ : ∃ m, VG.Proof.Pbkdf2.Md.Arm.Iterate.nn s₀ = m + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero hne).symm⟩
      rw [hm] at i
      rw [← hq.nn, hm] at i'
      exact VG.Proof.Pbkdf2.Md.Arm.Iterate.loop_rel hz hp hp' hq hH.out hH.reloc hH.comp hc _ _ _ _ _ _ ⟨i, i'⟩ e e'
  have epi : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc hH.md s₀ 0 s ∧ VG.Proof.Pbkdf2.Md.Arm.Iterate.Inv H sc hH.md s₀' 0 s') (.block H.st.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r11]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.1.r11, h.2.r11, VG.Proof.Pbkdf2.Md.Arm.Iterate.scr, VG.Proof.Pbkdf2.Md.Arm.Iterate.scr, hq.a0]) hep
  unfold Hash.iterate
  exact pro.seq (br.seq epi)

/-! ## Verified -/

theorem pubEq_of {S : Spec.Hmac.StreamingHash} {W : Nat} {s₁ s₂ : State} (h : (iterG S W).pub s₁ s₂) :
    VG.Proof.Pbkdf2.Md.Arm.Iterate.PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- `iterate` is verified against `iterG`, for any hash function the proof
supports (`HashOK`), whose pieces of code the taint analysis accepts
(`Checks`). -/
theorem verified {H : Hash} (hH : VG.Proof.Pbkdf2.Md.Arm.HashOK H) (hc : VG.Proof.Pbkdf2.Md.Arm.Iterate.Checks H) {sc : Nat} (hfit : H.st.buf + H.N + H.B ≤ 8 * sc)
    (hsat : ∃ s, (iterG hH.SH sc).pre s) :
    Verified Arm.target H.iterate (iterG hH.SH sc) := by
  refine ⟨fun s hs => VG.Proof.Pbkdf2.Md.Arm.Iterate.correct hH (VG.Proof.Pbkdf2.Md.Arm.Iterate.pre_of hH hs hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  exact (VG.Proof.Pbkdf2.Md.Arm.Iterate.iterate_rel hH hc (VG.Proof.Pbkdf2.Md.Arm.Iterate.pre_of hH h₁ hfit) (VG.Proof.Pbkdf2.Md.Arm.Iterate.pre_of hH h₂ hfit) (VG.Proof.Pbkdf2.Md.Arm.Iterate.pubEq_of hpub) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.Arm.Iterate

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Sha512`. -/
section

/-!
# The SHA-512 family's digest on ARMv7

The streaming `finalize`'s code writing the final hash value
(`Impl.Sha512.Arm.Stream.outW`, each 64-bit word big-endian, from its halves
stored low first) writes the digest of `Proof.Sha512.md` (`OutOk`), as HMAC
and PBKDF2 use it.
-/

namespace VG.Proof.Pbkdf2.Md.Arm

open VG VG.Arm
open VG.Impl.Sha512.Arm (lo hi)
open VG.Impl.Sha512.Arm.Stream (outW)
open VG.Proof.MdStream.Arm (wp_ldr wp_str wp_rev)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append writeBytes_frame)
open VG.Proof.Sha512.Arm.Stream.Finalize (wordBytes_split writeW_rev flat_length)
open VG.Proof.Sha512.Arm (readW_lo readW_hi)
open VG.Spec.Sha512 (HashValue stateAt wordBytes)

/-- The first `n` words of the final hash value at `p0` (`r0`), big-endian, to `p6` (`r6`). -/
theorem out64_ok {p0 p6 : BitVec 32} (f0 : p0.toNat + 64 ≤ 2 ^ 32) (f6 : p6.toNat + 64 ≤ 2 ^ 32)
    (hd : Region.Disjoint ⟨State.addr p0, 64⟩ ⟨State.addr p6, 64⟩) :
    ∀ n ≤ 8, ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .r0 = p0 → s.gpr .r6 = p6 →
    InRegions (s.rd ++ s.wr) (State.addr p0) 64 → InRegions s.wr (State.addr p6) 64 →
    (∀ s', (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr p6) (((stateAt s.mem (State.addr p0)).toList.take n).flatMap wordBytes) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap outW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ k
    exact k s (fun _ _ _ => rfl) rfl rfl rfl (by simp [VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q h0 h6 hin hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q h0 h6 hin hout fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    have hP := VG.Proof.Sha512.Arm.Stream.Finalize.flat_length (stateAt s.mem (State.addr p0)) n (by omega)
    simp only [outW, List.cons_append, List.nil_append]
    have i₀ : ∀ o, o + 4 ≤ 8 → InRegions (s₁.rd ++ s₁.wr) (State.addr p0 + BitVec.ofNat 64 (8 * n + o)) 4 :=
      fun o ho => by
        rw [rd₁, wr₁]; exact MdStream.Arm.InRegions.offset hin (by omega) (by omega)
    have o₀ : ∀ o, o + 4 ≤ 8 → InRegions s₁.wr (State.addr p6 + BitVec.ofNat 64 (8 * n + o)) 4 :=
      fun o ho => by rw [wr₁]; exact MdStream.Arm.InRegions.offset hout (by omega) (by omega)
    refine wp_ldr (a := State.addr p0 + BitVec.ofNat 64 (8 * n + 0)) (by omega)
      (by rw [g₁ _ (by decide) (by decide), h0, addr_add (by omega)]; rfl) (i₀ 0 (by omega)) fun s₂ u₂ => ?_
    refine wp_ldr (a := State.addr p0 + BitVec.ofNat 64 (8 * n + 4)) (by omega)
      (by rw [u₂.other _ (by decide), g₁ _ (by decide) (by decide), h0, addr_add (by omega)])
      (by rw [u₂.rd, u₂.wr]; exact i₀ 4 (by omega)) fun s₃ u₃ => wp_rev fun s₄ u₄ => wp_rev fun s₅ u₅ => ?_
    have e6 : s₅.gpr .r6 = p6 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        g₁ _ (by decide) (by decide), h6]
    refine wp_str (a := State.addr p6 + BitVec.ofNat 64 (8 * n + 0)) (by omega)
      (by rw [e6, addr_add (by omega)]; rfl) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr]; exact o₀ 0 (by omega)) fun s₆ g₆ => ?_
    refine wp_str (a := State.addr p6 + BitVec.ofNat 64 (8 * n + 4)) (by omega)
      (by rw [g₆.gpr, e6, addr_add (by omega)]) (by rw [g₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]; exact o₀ 4 (by omega))
      fun s₇ g₇ => k s₇ (fun r h9 h10 => by
          rw [g₇.gpr, g₆.gpr, u₅.other r h9, u₄.other r h10, u₃.other r h10, u₂.other r h9, g₁ r h9 h10])
        (by rw [g₇.rd, g₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [g₇.wr, g₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
        (by rw [g₇.sp, g₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]) ?_
    -- The word's halves, as in `s`: the writes so far are to `p6`.
    have hread : ∀ o, o + 4 ≤ 8 → s₁.mem.readW (State.addr p0 + BitVec.ofNat 64 (8 * n + o)) 32 =
        s.mem.readW (State.addr p0 + BitVec.ofNat 64 (8 * n + o)) 32 := by
      intro o ho
      rw [m₁]
      refine (VG.WriteBytes.writeBytes_frame s.mem (State.addr p6) _ (R := ⟨State.addr p6, 64⟩) ?_).readW
        (r := ⟨State.addr p0 + BitVec.ofNat 64 (8 * n + o), 4⟩) (Region.contains_self _ _) ?_ (by decide)
      · rw [hP]; exact Memory.contains_base (by omega)
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hd.sub_left (Offset.sub_base _ (by omega))
    have hw : (stateAt s.mem (State.addr p0))[n] = s.mem.readW (State.addr p0 + BitVec.ofNat 64 (8 * n)) 64 := by
      simp [stateAt]
    have wlo : s.mem.readW (State.addr p0 + BitVec.ofNat 64 (8 * n + 0)) 32 = lo (stateAt s.mem (State.addr p0))[n] := by
      rw [hw, readW_lo, Nat.add_zero]
    have whi : s.mem.readW (State.addr p0 + BitVec.ofNat 64 (8 * n + 4)) 32 = hi (stateAt s.mem (State.addr p0))[n] := by
      rw [hw, readW_hi, BitVec.ofNat_add, ← BitVec.add_assoc]; rfl
    have v10 : s₅.gpr .r10 = rev (hi (stateAt s.mem (State.addr p0))[n]) := by
      rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.mem, hread 4 (by omega), whi]
    have v9 : s₆.gpr .r9 = rev (lo (stateAt s.mem (State.addr p0))[n]) := by
      rw [g₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hread 0 (by omega), wlo]
    have a4 : State.addr p6 + BitVec.ofNat 64 (8 * n + 4) =
        State.addr p6 + BitVec.ofNat 64 (8 * n + 0) +
          BitVec.ofNat 64 (Spec.Sha256.wordBytes (hi (stateAt s.mem (State.addr p0))[n])).length := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]; rfl
    have a8 : State.addr p6 + BitVec.ofNat 64 (8 * n + 0) = State.addr p6 +
        BitVec.ofNat 64 (((stateAt s.mem (State.addr p0)).toList.take n).flatMap wordBytes).length := by
      rw [hP]; rfl
    rw [g₇.mem, v9, g₆.mem, v10, u₅.mem, u₄.mem, u₃.mem, u₂.mem, VG.Proof.Sha512.Arm.Stream.Finalize.writeW_rev, VG.Proof.Sha512.Arm.Stream.Finalize.writeW_rev, a4,
      VG.WriteBytes.writeBytes_append _ _ _ _ (by simp [Spec.Sha256.wordBytes]), ← wordBytes_split, m₁, a8,
      VG.WriteBytes.writeBytes_append _ _ _ _ (by rw [hP]; simp [wordBytes]; omega), List.take_add_one,
      List.getElem?_eq_getElem (by simp; omega), Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, Vector.getElem_toList]

/-- The SHA-512 family's digest code, as HMAC and PBKDF2 use it. -/
theorem sha512_out : VG.Proof.Pbkdf2.Md.Arm.OutOk Proof.Sha512.md ((List.range 8).flatMap outW) := by
  intro s f₀ f₆ hin hout hd
  rw [← List.append_nil ((List.range 8).flatMap outW)]
  refine VG.Proof.Pbkdf2.Md.Arm.out64_ok f₀ f₆ hd 8 (Nat.le_refl _) [] s _ rfl rfl hin hout fun s' g rd wr sp m => WP.block_nil
    ⟨g, rd, wr, sp, ?_⟩
  rw [m, List.take_of_length_le (by simp)]
  rfl

end VG.Proof.Pbkdf2.Md.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Instances`. -/
section

/-!
# HMAC and PBKDF2-HMAC over Merkle–Damgård hash functions on ARMv7: the instances

MD5, SHA-1 and the SHA-512 family as `Hash`es (their streaming functions as
the code calls them, `Proof/Pbkdf2/Stream/Arm/Hashes.lean`, with their hash
value, length field, digest code and compression function), what the proofs
need of them (`HashOK`, from the hash functions' own proofs), and the generic
proofs of HMAC's `init` and `finalize` and PBKDF2's iteration
(`HmacInitCT.lean`, `HmacFinCT.lean`, `IterateCT.lean`) at each of them, moved
to the shared contracts of `Spec/Hmac/Generic.lean` and
`Spec/Pbkdf2/Generic.lean`, which the artifacts are emitted with. SHA-256 and
SHA-224 are in `Sha256.lean` and `Sha224.lean`.
-/

namespace VG.Proof.Pbkdf2.Md.Arm

open VG VG.Arm VG.Proof.MdStream
open VG.Impl.Pbkdf2.Md.Arm (Hash)
open VG.Proof.Pbkdf2.Stream.Arm (iterG below sha1H md5H sha384H sha512H' sha512_224H sha512_256H sha1OK md5OK
  sha384OK sha512OK sha512_224OK sha512_256OK)

/-! ## The hash functions -/

/-- SHA-1: a 20-byte hash value, a big-endian length field, and
`vg_sha1_compress`, with 112 bytes of scratch space. -/
def sha1Md : Hash where
  st := sha1H
  N := 20
  L := 8
  be := true
  so := 112
  out := Impl.Sha1.Arm.Stream.params.out
  compN := "vg_sha1_compress"
  compC := Impl.Sha1.Arm.compress

/-- MD5: a 16-byte hash value, a little-endian length field, and
`vg_md5_compress`, with 64 bytes of scratch space. -/
def md5Md : Hash where
  st := md5H
  N := 16
  L := 8
  be := false
  so := 64
  out := Impl.Md5.Arm.Stream.params.out
  compN := "vg_md5_compress"
  compC := Impl.Md5.Arm.compress

/-- The member of the SHA-512 family with a `D`-byte digest, initial hash
value `iv` and streaming `init` named `initN`: a 64-byte hash value, a
16-byte big-endian length field, and `vg_sha512_compress`, with 224 bytes of
scratch space. -/
def sha512Md (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) : Hash where
  st := Pbkdf2.Stream.Arm.sha512H D initN iv
  N := 64
  L := 16
  be := true
  so := 224
  out := (List.range 8).flatMap Impl.Sha512.Arm.Stream.outW
  compN := "vg_sha512_compress"
  compC := Impl.Sha512.Arm.compress

def sha384Md : Hash := VG.Proof.Pbkdf2.Md.Arm.sha512Md 48 "vg_sha384_init" Spec.Sha512.H0_384
def sha512Md' : Hash := VG.Proof.Pbkdf2.Md.Arm.sha512Md 64 "vg_sha512_init" Spec.Sha512.H0_512
def sha512_224Md : Hash := VG.Proof.Pbkdf2.Md.Arm.sha512Md 28 "vg_sha512_224_init" Spec.Sha512.H0_512_224
def sha512_256Md : Hash := VG.Proof.Pbkdf2.Md.Arm.sha512Md 32 "vg_sha512_256_init" Spec.Sha512.H0_512_256

/-! ## What the proofs need of them -/

theorem sha1_comp : VG.Proof.Pbkdf2.Md.Arm.CompOk Proof.Sha1.md 112 Impl.Sha1.Arm.compress :=
  ⟨Proof.Sha1.Arm.compress_verified.1, Proof.Sha1.Arm.compress_verified.2.1, by lit_decide,
    by rw [← Code.allInstrs_eq]; lit_decide⟩

def sha1MdOK : VG.Proof.Pbkdf2.Md.Arm.HashOK VG.Proof.Pbkdf2.Md.Arm.sha1Md where
  md := Proof.Sha1.md
  out := OutOk.ofShape Proof.Sha1.Arm.Stream.shape
  comp := VG.Proof.Pbkdf2.Md.Arm.sha1_comp
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha1.md, Spec.Sha1.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 20) h (by omega)
  len := by decide
  stream := sha1OK
  iv := Spec.Sha1.H0
  repr _ _ _ h := h
  back _ _ _ h := h
  hash m := by
    show Spec.Sha1.hash m = _
    rw [Proof.Sha1.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha1.md.digest_length _))).symm
  sizes := ⟨.inl rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

theorem md5_comp : VG.Proof.Pbkdf2.Md.Arm.CompOk Proof.Md5.md 64 Impl.Md5.Arm.compress :=
  ⟨Proof.Md5.Arm.compress_verified.1, Proof.Md5.Arm.compress_verified.2.1, by decide +kernel,
    by rw [← Code.allInstrs_eq]; decide +kernel⟩

def md5MdOK : VG.Proof.Pbkdf2.Md.Arm.HashOK VG.Proof.Pbkdf2.Md.Arm.md5Md where
  md := Proof.Md5.md
  out := OutOk.ofShape Proof.Md5.Arm.Stream.shape
  comp := VG.Proof.Pbkdf2.Md.Arm.md5_comp
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Md5.md, Spec.Md5.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 16) h (by omega)
  len := by decide
  stream := md5OK
  iv := Spec.Md5.H0
  repr _ _ _ h := h
  back _ _ _ h := h
  hash m := by
    show Spec.Md5.hash m = _
    rw [Proof.Md5.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Md5.md.digest_length _))).symm
  sizes := ⟨.inl rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

theorem sha512_comp : VG.Proof.Pbkdf2.Md.Arm.CompOk Proof.Sha512.md 224 Impl.Sha512.Arm.compress :=
  ⟨Proof.Sha512.Arm.Compress.compress_verified.1, Proof.Sha512.Arm.Compress.compress_verified.2.1, by lit_decide,
    by rw [← Code.allInstrs_eq]; lit_decide⟩

/-- `HashOK` for the member of the SHA-512 family with a `D`-byte digest, from
the initial hash value `iv`. -/
def sha512MdOK {D : Nat} {initN : String} {iv : Spec.Sha512.HashValue}
    (hs : Pbkdf2.Stream.Arm.HashOK (Pbkdf2.Stream.Arm.sha512H D initN iv))
    (hR : hs.SH.Repr = Spec.Sha512.Repr iv) (hh : ∀ m, hs.SH.H.hash m = (Spec.Sha512.finalHash iv m).take D)
    (hz : VG.Proof.Pbkdf2.Md.Arm.Sizes (VG.Proof.Pbkdf2.Md.Arm.sha512Md D initN iv))
    (hlen : VG.Proof.Pbkdf2.Md.Arm.wordsBytes (Impl.Pbkdf2.Md.Arm.lenWords true 16 (128 + D)) = Proof.Sha512.md.lenBytes (128 + D)) :
    VG.Proof.Pbkdf2.Md.Arm.HashOK (VG.Proof.Pbkdf2.Md.Arm.sha512Md D initN iv) where
  md := Proof.Sha512.md
  out := VG.Proof.Pbkdf2.Md.Arm.sha512_out
  comp := VG.Proof.Pbkdf2.Md.Arm.sha512_comp
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega)
  len := hlen
  stream := hs
  iv := iv
  repr mem p m h := by rw [hR] at h; exact Proof.Sha512.repr_iff.mp h
  back mem p m h := by rw [hR]; exact Proof.Sha512.repr_iff.mpr h
  hash m := by rw [hh, Proof.Sha512.finalHash_eq]; rfl
  sizes := hz

def sha384MdOK : VG.Proof.Pbkdf2.Md.Arm.HashOK VG.Proof.Pbkdf2.Md.Arm.sha384Md :=
  VG.Proof.Pbkdf2.Md.Arm.sha512MdOK sha384OK rfl (fun _ => rfl)
    ⟨.inr rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide⟩ (by decide)

def sha512MdOK' : VG.Proof.Pbkdf2.Md.Arm.HashOK VG.Proof.Pbkdf2.Md.Arm.sha512Md' :=
  VG.Proof.Pbkdf2.Md.Arm.sha512MdOK sha512OK rfl
    (fun m => (List.take_of_length_le (Nat.le_of_eq (Hmac.Generic.Common.finalHash_length _ m))).symm)
    ⟨.inr rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide⟩ (by decide)

def sha512_224MdOK : VG.Proof.Pbkdf2.Md.Arm.HashOK VG.Proof.Pbkdf2.Md.Arm.sha512_224Md :=
  VG.Proof.Pbkdf2.Md.Arm.sha512MdOK sha512_224OK rfl (fun _ => rfl)
    ⟨.inr rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide⟩ (by decide)

def sha512_256MdOK : VG.Proof.Pbkdf2.Md.Arm.HashOK VG.Proof.Pbkdf2.Md.Arm.sha512_256Md :=
  VG.Proof.Pbkdf2.Md.Arm.sha512MdOK sha512_256OK rfl (fun _ => rfl)
    ⟨.inr rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide⟩ (by decide)

end VG.Proof.Pbkdf2.Md.Arm

namespace VG.Proof.Pbkdf2.Md.Arm.Instances

open VG.Arm
open VG.Proof.Pbkdf2.Md.Arm
open VG.Proof.Pbkdf2.Stream.Arm (initG finG iterG below count)

/-- A state satisfying `init`'s precondition, with states of `S` bytes and
`8 sc` bytes of scratch space (and a one-byte key); `scratch`, at `0x4000`,
is the stack argument. -/
def initSat (S sc : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 1
    | _ => 0
  sp := 0x6000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x6001 then 0x40 else 0
  rd := [⟨0x3000, 1⟩, ⟨0x6000, 4⟩]
  wr := [⟨0x1000, S⟩, ⟨0x2000, S⟩, ⟨0x4000, 8 * sc⟩]

/-- A state satisfying `finalize`'s precondition, with states of `S` bytes,
a digest of `D` bytes and `8 sc` bytes of scratch space; `out`, at `0x3000`,
and `scratch`, at `0x4000`, are the stack arguments. -/
def finSat (S D sc : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000
    | _ => 0
  sp := 0x6000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x6001 then 0x30 else if a = 0x6005 then 0x40 else 0
  rd := [⟨0x2000, S⟩, ⟨0x6000, 8⟩]
  wr := [⟨0x1000, S⟩, ⟨0x3000, D⟩, ⟨0x4000, 8 * sc⟩]

/-- `initG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem initImp (S : Spec.Hmac.StreamingHash) (W : Nat) (h : ∃ s, (Spec.Hmac.initScratchContract S W Arm.abi 16).pre s) :
    (initG S W).Implies (Spec.Hmac.initScratchContract S W Arm.abi 16) := by
  generic_implies [
    Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost, initG, below, count, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using h

/-- `finG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem finImp (S : Spec.Hmac.StreamingHash) (W : Nat) (h : ∃ s, (Spec.Hmac.finalizeScratchContract S W Arm.abi 16).pre s) :
    (finG S W).Implies (Spec.Hmac.finalizeScratchContract S W Arm.abi 16) := by
  generic_implies [
    Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, finG, below, count, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using h

/-- A state satisfying `iterate`'s precondition, with states of `S` bytes, a
digest of `D` bytes and `8 sc` bytes of scratch space; `scratch`, at
`0x4000`, is the stack argument. -/
def iterSat (S D sc : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r3 => 0x3000
    | _ => 0
  sp := 0x6000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x6001 then 0x40 else 0
  rd := [⟨0x1000, 2 * S⟩, ⟨0x2000, D⟩, ⟨0x6000, 4⟩]
  wr := [⟨0x3000, D⟩, ⟨0x4000, 8 * sc⟩]

/-- `iterG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem iterImp (S : Spec.Hmac.StreamingHash) (W : Nat) (h : ∃ s, (Spec.Pbkdf2.iterateContract S W Arm.abi 16).pre s) :
    (iterG S W).Implies (Spec.Pbkdf2.iterateContract S W Arm.abi 16) := by
  generic_implies [
    Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, iterG, below, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using h

/-! ## SHA-1 -/

theorem sha1_iterChecks : Iterate.Checks VG.Proof.Pbkdf2.Md.Arm.sha1Md := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

theorem sha1_finChecks : Fin.Checks VG.Proof.Pbkdf2.Md.Arm.sha1Md := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

theorem sha1_iterImp : (iterG Spec.Hmac.sha1S 56).Implies (Spec.Hmac.sha1I.iterateContract Arm.abi 16) :=
  VG.Proof.Pbkdf2.Md.Arm.Instances.iterImp Spec.Hmac.sha1S 56 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha1S, Spec.Hmac.sha1, iterG, below,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using VG.Proof.Pbkdf2.Md.Arm.Instances.iterSat 84 20 56)

theorem sha1_iterate : Verified Arm.target sha1Md.iterate (Spec.Hmac.sha1I.iterateContract Arm.abi 16) :=
  (Iterate.verified VG.Proof.Pbkdf2.Md.Arm.sha1MdOK VG.Proof.Pbkdf2.Md.Arm.Instances.sha1_iterChecks (by decide) sha1_iterImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.Arm.Instances.sha1_iterImp

theorem sha1_initChecks : HmacInit.Checks VG.Proof.Pbkdf2.Md.Arm.sha1Md := by
  refine ⟨⟨?_, ?_⟩,
    List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_nil _⟩⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩⟩
  taint_decide_all

theorem sha1_initImp : (initG Spec.Hmac.sha1S 56).Implies (Spec.Hmac.sha1I.initScratchContract Arm.abi 16) :=
  VG.Proof.Pbkdf2.Md.Arm.Instances.initImp Spec.Hmac.sha1S 56 (by
    inst_sat [Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha1S, Spec.Hmac.sha1, initG, below,
      count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using VG.Proof.Pbkdf2.Md.Arm.Instances.initSat 84 56)

theorem sha1_finImp : (finG Spec.Hmac.sha1S 56).Implies (Spec.Hmac.sha1I.finalizeScratchContract Arm.abi 16) :=
  VG.Proof.Pbkdf2.Md.Arm.Instances.finImp Spec.Hmac.sha1S 56 (by
    inst_sat [Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha1S, Spec.Hmac.sha1, finG,
      below, count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using VG.Proof.Pbkdf2.Md.Arm.Instances.finSat 84 20 56)

theorem sha1_init : Verified Arm.target sha1Md.hmacInit (Spec.Hmac.sha1I.initScratchContract Arm.abi 16) :=
  (HmacInit.verified VG.Proof.Pbkdf2.Md.Arm.sha1MdOK VG.Proof.Pbkdf2.Md.Arm.Instances.sha1_initChecks (by decide) sha1_initImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.Arm.Instances.sha1_initImp

theorem sha1_finalize : Verified Arm.target sha1Md.hmacFin (Spec.Hmac.sha1I.finalizeScratchContract Arm.abi 16) :=
  (Fin.verified VG.Proof.Pbkdf2.Md.Arm.sha1MdOK VG.Proof.Pbkdf2.Md.Arm.Instances.sha1_finChecks (by decide) sha1_finImp.sat_left).of_implies
    VG.Proof.Pbkdf2.Md.Arm.Instances.sha1_finImp

/-! ## MD5 -/

theorem md5_iterChecks : Iterate.Checks VG.Proof.Pbkdf2.Md.Arm.md5Md := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

theorem md5_finChecks : Fin.Checks VG.Proof.Pbkdf2.Md.Arm.md5Md := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

theorem md5_iterImp : (iterG Spec.Hmac.md5S 48).Implies (Spec.Hmac.md5I.iterateContract Arm.abi 16) :=
  VG.Proof.Pbkdf2.Md.Arm.Instances.iterImp Spec.Hmac.md5S 48 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.md5S, Spec.Hmac.md5, iterG, below,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using VG.Proof.Pbkdf2.Md.Arm.Instances.iterSat 80 16 48)

theorem md5_iterate : Verified Arm.target md5Md.iterate (Spec.Hmac.md5I.iterateContract Arm.abi 16) :=
  (Iterate.verified VG.Proof.Pbkdf2.Md.Arm.md5MdOK VG.Proof.Pbkdf2.Md.Arm.Instances.md5_iterChecks (by decide) md5_iterImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.Arm.Instances.md5_iterImp

theorem md5_initChecks : HmacInit.Checks VG.Proof.Pbkdf2.Md.Arm.md5Md := by
  refine ⟨⟨?_, ?_⟩,
    List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_nil _⟩⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩⟩
  taint_decide_all

theorem md5_initImp : (initG Spec.Hmac.md5S 48).Implies (Spec.Hmac.md5I.initScratchContract Arm.abi 16) :=
  VG.Proof.Pbkdf2.Md.Arm.Instances.initImp Spec.Hmac.md5S 48 (by
    inst_sat [Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.md5S, Spec.Hmac.md5, initG, below,
      count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using VG.Proof.Pbkdf2.Md.Arm.Instances.initSat 80 48)

theorem md5_finImp : (finG Spec.Hmac.md5S 48).Implies (Spec.Hmac.md5I.finalizeScratchContract Arm.abi 16) :=
  VG.Proof.Pbkdf2.Md.Arm.Instances.finImp Spec.Hmac.md5S 48 (by
    inst_sat [Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.md5S, Spec.Hmac.md5, finG,
      below, count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using VG.Proof.Pbkdf2.Md.Arm.Instances.finSat 80 16 48)

theorem md5_init : Verified Arm.target md5Md.hmacInit (Spec.Hmac.md5I.initScratchContract Arm.abi 16) :=
  (HmacInit.verified VG.Proof.Pbkdf2.Md.Arm.md5MdOK VG.Proof.Pbkdf2.Md.Arm.Instances.md5_initChecks (by decide) md5_initImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.Arm.Instances.md5_initImp

theorem md5_finalize : Verified Arm.target md5Md.hmacFin (Spec.Hmac.md5I.finalizeScratchContract Arm.abi 16) :=
  (Fin.verified VG.Proof.Pbkdf2.Md.Arm.md5MdOK VG.Proof.Pbkdf2.Md.Arm.Instances.md5_finChecks (by decide) md5_finImp.sat_left).of_implies
    VG.Proof.Pbkdf2.Md.Arm.Instances.md5_finImp

/-! ## SHA-384 -/

theorem sha384_iterChecks : Iterate.Checks VG.Proof.Pbkdf2.Md.Arm.sha384Md := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

theorem sha384_finChecks : Fin.Checks VG.Proof.Pbkdf2.Md.Arm.sha384Md := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

theorem sha384_iterImp : (iterG Spec.Hmac.sha384S 234).Implies (Spec.Hmac.sha384I.iterateContract Arm.abi 16) :=
  VG.Proof.Pbkdf2.Md.Arm.Instances.iterImp Spec.Hmac.sha384S 234 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha384S, Spec.Hmac.sha384, iterG, below,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using VG.Proof.Pbkdf2.Md.Arm.Instances.iterSat 192 48 234)

theorem sha384_iterate : Verified Arm.target sha384Md.iterate (Spec.Hmac.sha384I.iterateContract Arm.abi 16) :=
  (Iterate.verified VG.Proof.Pbkdf2.Md.Arm.sha384MdOK VG.Proof.Pbkdf2.Md.Arm.Instances.sha384_iterChecks (by decide) sha384_iterImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.Arm.Instances.sha384_iterImp

theorem sha384_initChecks : HmacInit.Checks VG.Proof.Pbkdf2.Md.Arm.sha384Md := by
  refine ⟨⟨?_, ?_⟩,
    List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_nil _⟩⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩⟩
  taint_decide_all

theorem sha384_initImp : (initG Spec.Hmac.sha384S 234).Implies (Spec.Hmac.sha384I.initScratchContract Arm.abi 16) :=
  VG.Proof.Pbkdf2.Md.Arm.Instances.initImp Spec.Hmac.sha384S 234 (by
    inst_sat [Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha384S, Spec.Hmac.sha384, initG, below,
      count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using VG.Proof.Pbkdf2.Md.Arm.Instances.initSat 192 234)

theorem sha384_finImp : (finG Spec.Hmac.sha384S 234).Implies (Spec.Hmac.sha384I.finalizeScratchContract Arm.abi 16) :=
  VG.Proof.Pbkdf2.Md.Arm.Instances.finImp Spec.Hmac.sha384S 234 (by
    inst_sat [Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha384S, Spec.Hmac.sha384, finG,
      below, count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using VG.Proof.Pbkdf2.Md.Arm.Instances.finSat 192 48 234)

theorem sha384_init : Verified Arm.target sha384Md.hmacInit (Spec.Hmac.sha384I.initScratchContract Arm.abi 16) :=
  (HmacInit.verified VG.Proof.Pbkdf2.Md.Arm.sha384MdOK VG.Proof.Pbkdf2.Md.Arm.Instances.sha384_initChecks (by decide) sha384_initImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.Arm.Instances.sha384_initImp

theorem sha384_finalize : Verified Arm.target sha384Md.hmacFin (Spec.Hmac.sha384I.finalizeScratchContract Arm.abi 16) :=
  (Fin.verified VG.Proof.Pbkdf2.Md.Arm.sha384MdOK VG.Proof.Pbkdf2.Md.Arm.Instances.sha384_finChecks (by decide) sha384_finImp.sat_left).of_implies
    VG.Proof.Pbkdf2.Md.Arm.Instances.sha384_finImp

/-! ## SHA-512 -/

theorem sha512_iterChecks : Iterate.Checks VG.Proof.Pbkdf2.Md.Arm.sha512Md' := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

theorem sha512_finChecks : Fin.Checks VG.Proof.Pbkdf2.Md.Arm.sha512Md' := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

theorem sha512_iterImp : (iterG Spec.Hmac.sha512S 234).Implies (Spec.Hmac.sha512I.iterateContract Arm.abi 16) :=
  VG.Proof.Pbkdf2.Md.Arm.Instances.iterImp Spec.Hmac.sha512S 234 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512S, Spec.Hmac.sha512, iterG, below,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using VG.Proof.Pbkdf2.Md.Arm.Instances.iterSat 192 64 234)

theorem sha512_iterate : Verified Arm.target sha512Md'.iterate (Spec.Hmac.sha512I.iterateContract Arm.abi 16) :=
  (Iterate.verified VG.Proof.Pbkdf2.Md.Arm.sha512MdOK' VG.Proof.Pbkdf2.Md.Arm.Instances.sha512_iterChecks (by decide) sha512_iterImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.Arm.Instances.sha512_iterImp

theorem sha512_initChecks : HmacInit.Checks VG.Proof.Pbkdf2.Md.Arm.sha512Md' := by
  refine ⟨⟨?_, ?_⟩,
    List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_nil _⟩⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩⟩
  taint_decide_all

theorem sha512_initImp : (initG Spec.Hmac.sha512S 234).Implies (Spec.Hmac.sha512I.initScratchContract Arm.abi 16) :=
  VG.Proof.Pbkdf2.Md.Arm.Instances.initImp Spec.Hmac.sha512S 234 (by
    inst_sat [Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha512S, Spec.Hmac.sha512, initG, below,
      count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using VG.Proof.Pbkdf2.Md.Arm.Instances.initSat 192 234)

theorem sha512_finImp : (finG Spec.Hmac.sha512S 234).Implies (Spec.Hmac.sha512I.finalizeScratchContract Arm.abi 16) :=
  VG.Proof.Pbkdf2.Md.Arm.Instances.finImp Spec.Hmac.sha512S 234 (by
    inst_sat [Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha512S, Spec.Hmac.sha512, finG,
      below, count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using VG.Proof.Pbkdf2.Md.Arm.Instances.finSat 192 64 234)

theorem sha512_init : Verified Arm.target sha512Md'.hmacInit (Spec.Hmac.sha512I.initScratchContract Arm.abi 16) :=
  (HmacInit.verified VG.Proof.Pbkdf2.Md.Arm.sha512MdOK' VG.Proof.Pbkdf2.Md.Arm.Instances.sha512_initChecks (by decide) sha512_initImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.Arm.Instances.sha512_initImp

theorem sha512_finalize : Verified Arm.target sha512Md'.hmacFin (Spec.Hmac.sha512I.finalizeScratchContract Arm.abi 16) :=
  (Fin.verified VG.Proof.Pbkdf2.Md.Arm.sha512MdOK' VG.Proof.Pbkdf2.Md.Arm.Instances.sha512_finChecks (by decide) sha512_finImp.sat_left).of_implies
    VG.Proof.Pbkdf2.Md.Arm.Instances.sha512_finImp

/-! ## SHA-512/224 -/

theorem sha512_224_iterChecks : Iterate.Checks VG.Proof.Pbkdf2.Md.Arm.sha512_224Md := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

theorem sha512_224_finChecks : Fin.Checks VG.Proof.Pbkdf2.Md.Arm.sha512_224Md := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

theorem sha512_224_iterImp : (iterG Spec.Hmac.sha512_224S 234).Implies (Spec.Hmac.sha512_224I.iterateContract Arm.abi 16) :=
  VG.Proof.Pbkdf2.Md.Arm.Instances.iterImp Spec.Hmac.sha512_224S 234 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, iterG, below,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using VG.Proof.Pbkdf2.Md.Arm.Instances.iterSat 192 28 234)

theorem sha512_224_iterate : Verified Arm.target sha512_224Md.iterate (Spec.Hmac.sha512_224I.iterateContract Arm.abi 16) :=
  (Iterate.verified VG.Proof.Pbkdf2.Md.Arm.sha512_224MdOK VG.Proof.Pbkdf2.Md.Arm.Instances.sha512_224_iterChecks (by decide) sha512_224_iterImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.Arm.Instances.sha512_224_iterImp

theorem sha512_224_initChecks : HmacInit.Checks VG.Proof.Pbkdf2.Md.Arm.sha512_224Md := by
  refine ⟨⟨?_, ?_⟩,
    List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_nil _⟩⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩⟩
  taint_decide_all

theorem sha512_224_initImp : (initG Spec.Hmac.sha512_224S 234).Implies (Spec.Hmac.sha512_224I.initScratchContract Arm.abi 16) :=
  VG.Proof.Pbkdf2.Md.Arm.Instances.initImp Spec.Hmac.sha512_224S 234 (by
    inst_sat [Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, initG, below,
      count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using VG.Proof.Pbkdf2.Md.Arm.Instances.initSat 192 234)

theorem sha512_224_finImp : (finG Spec.Hmac.sha512_224S 234).Implies (Spec.Hmac.sha512_224I.finalizeScratchContract Arm.abi 16) :=
  VG.Proof.Pbkdf2.Md.Arm.Instances.finImp Spec.Hmac.sha512_224S 234 (by
    inst_sat [Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, finG,
      below, count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using VG.Proof.Pbkdf2.Md.Arm.Instances.finSat 192 28 234)

theorem sha512_224_init : Verified Arm.target sha512_224Md.hmacInit (Spec.Hmac.sha512_224I.initScratchContract Arm.abi 16) :=
  (HmacInit.verified VG.Proof.Pbkdf2.Md.Arm.sha512_224MdOK VG.Proof.Pbkdf2.Md.Arm.Instances.sha512_224_initChecks (by decide) sha512_224_initImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.Arm.Instances.sha512_224_initImp

theorem sha512_224_finalize : Verified Arm.target sha512_224Md.hmacFin (Spec.Hmac.sha512_224I.finalizeScratchContract Arm.abi 16) :=
  (Fin.verified VG.Proof.Pbkdf2.Md.Arm.sha512_224MdOK VG.Proof.Pbkdf2.Md.Arm.Instances.sha512_224_finChecks (by decide) sha512_224_finImp.sat_left).of_implies
    VG.Proof.Pbkdf2.Md.Arm.Instances.sha512_224_finImp

/-! ## SHA-512/256 -/

theorem sha512_256_iterChecks : Iterate.Checks VG.Proof.Pbkdf2.Md.Arm.sha512_256Md := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

theorem sha512_256_finChecks : Fin.Checks VG.Proof.Pbkdf2.Md.Arm.sha512_256Md := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

theorem sha512_256_iterImp : (iterG Spec.Hmac.sha512_256S 234).Implies (Spec.Hmac.sha512_256I.iterateContract Arm.abi 16) :=
  VG.Proof.Pbkdf2.Md.Arm.Instances.iterImp Spec.Hmac.sha512_256S 234 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, iterG, below,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using VG.Proof.Pbkdf2.Md.Arm.Instances.iterSat 192 32 234)

theorem sha512_256_iterate : Verified Arm.target sha512_256Md.iterate (Spec.Hmac.sha512_256I.iterateContract Arm.abi 16) :=
  (Iterate.verified VG.Proof.Pbkdf2.Md.Arm.sha512_256MdOK VG.Proof.Pbkdf2.Md.Arm.Instances.sha512_256_iterChecks (by decide) sha512_256_iterImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.Arm.Instances.sha512_256_iterImp

theorem sha512_256_initChecks : HmacInit.Checks VG.Proof.Pbkdf2.Md.Arm.sha512_256Md := by
  refine ⟨⟨?_, ?_⟩,
    List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_nil _⟩⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩⟩
  taint_decide_all

theorem sha512_256_initImp : (initG Spec.Hmac.sha512_256S 234).Implies (Spec.Hmac.sha512_256I.initScratchContract Arm.abi 16) :=
  VG.Proof.Pbkdf2.Md.Arm.Instances.initImp Spec.Hmac.sha512_256S 234 (by
    inst_sat [Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, initG, below,
      count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using VG.Proof.Pbkdf2.Md.Arm.Instances.initSat 192 234)

theorem sha512_256_finImp : (finG Spec.Hmac.sha512_256S 234).Implies (Spec.Hmac.sha512_256I.finalizeScratchContract Arm.abi 16) :=
  VG.Proof.Pbkdf2.Md.Arm.Instances.finImp Spec.Hmac.sha512_256S 234 (by
    inst_sat [Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, finG,
      below, count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using VG.Proof.Pbkdf2.Md.Arm.Instances.finSat 192 32 234)

theorem sha512_256_init : Verified Arm.target sha512_256Md.hmacInit (Spec.Hmac.sha512_256I.initScratchContract Arm.abi 16) :=
  (HmacInit.verified VG.Proof.Pbkdf2.Md.Arm.sha512_256MdOK VG.Proof.Pbkdf2.Md.Arm.Instances.sha512_256_initChecks (by decide) sha512_256_initImp.sat_left).of_implies VG.Proof.Pbkdf2.Md.Arm.Instances.sha512_256_initImp

theorem sha512_256_finalize : Verified Arm.target sha512_256Md.hmacFin (Spec.Hmac.sha512_256I.finalizeScratchContract Arm.abi 16) :=
  (Fin.verified VG.Proof.Pbkdf2.Md.Arm.sha512_256MdOK VG.Proof.Pbkdf2.Md.Arm.Instances.sha512_256_finChecks (by decide) sha512_256_finImp.sat_left).of_implies
    VG.Proof.Pbkdf2.Md.Arm.Instances.sha512_256_finImp

end VG.Proof.Pbkdf2.Md.Arm.Instances

end
