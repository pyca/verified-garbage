module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Wide
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.CopyLoop
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce

/-!
# Deterministic ECDSA on x86-64: `h` and `core`'s digest

From the digest of `D` bytes (`digest`, in `rsi`), into the frame
(`prep_ok`): `core`'s digest `Y` (and, for P-521, `h`) cleared
(`prepZero_ok`); a loop that copies the digest into them (`prepCopyA_ok`,
`prepCopyW_ok`), four bytes at a time, as many as `copyLen` computes: unless `wide`, its `min D Q` leftmost
bytes to the end of `Y`'s `Q`, which makes `X`, the `Q`-byte number
`bits2int` takes of the digest; if `wide`, the digest after `Q - D - 1` zero
bytes in `Y` (then one more), and after `Q - D` in `h`. Then, unless `wide`,
`h` is `X` modulo `n` (`reduce_ok`), and `core`'s digest is `X`; if `wide`,
`Y` shifted right by `8 - sh` bits is the digest's number shifted left by
`sh`, and `h` is the digest after `Q - D` zero bytes, RFC 6979's
`bits2octets` (`prepPost_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

/-- The words cleared, from `Y`. -/
abbrev nz (P : RfcHash) : Nat := if P.R.wide then 18 else 9

theorem zeroY_ok {t : State} (hc : Ctx L g m₀ t) : ∀ k ≤ 18, ∀ u : State,
    u.wr = t.wr → u.gpr .rsp = t.gpr .rsp → u.gpr .rcx = 0 →
    WP isa (.block ((List.range k).map fun j => .store (stk (fY + 8 * j)) .rcx)) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.gpr = u.gpr ∧ Frame [⟨L.B + BitVec.ofNat 64 240, 8 * k⟩] u.mem u'.mem ∧
      ∀ j < k, u'.mem.readW (L.B + BitVec.ofNat 64 240 + BitVec.ofNat 64 (8 * j)) 64 = 0
  | 0, _, u, _, _, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk, u, hwu, hsu, hcx => by
    have he := L.he
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeroY_ok hc k (by omega) u hwu hsu hcx) fun u₁ ⟨hrd, hwr, hg, hf, hz⟩ => ?_
    have w := hc.inFrW (d := 240 + 8 * k) (n := 8) (by omega) (by omega)
    rw [← hwu, ← hwr] at w
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_stk, hg, hsu, hcx, hc.rsp, fY,
      Offset.add_add, show 24 + (216 + 8 * k) = 240 + 8 * k by omega, w, ite_true, Option.some.injEq,
      exists_eq_left']
    have hw : Frame [⟨L.B + BitVec.ofNat 64 (240 + 8 * k), 8⟩] u₁.mem
        (u₁.mem.writeW (L.B + BitVec.ofNat 64 (240 + 8 * k)) (0 : BitVec 64)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have hf' : Frame [⟨L.B + BitVec.ofNat 64 240, 8 * (k + 1)⟩] u.mem
        (u₁.mem.writeW (L.B + BitVec.ofNat 64 (240 + 8 * k)) (0 : BitVec 64)) :=
      (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩).trans
      (hw.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)⟩)
    refine ⟨hrd, hwr, trivial, hf', fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have := hz j hj
      rw [Offset.add_add] at this
      rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact this
    · exact Mem.readW_writeW_self64 _ _ _

theorem zeros_bytes (n : Nat) :
    (List.range n).map (fun i => (0 : BitVec 64).extractLsb' (8 * (i % 8)) 8) = List.replicate n 0 := by
  rw [show (fun i => (0 : BitVec 64).extractLsb' (8 * (i % 8)) 8) = fun _ => (0 : BitVec 8) from
    funext fun i => by simp, List.map_const', List.length_range]

/-- `Y` (and, if `wide`, `h`) cleared. -/
theorem prepZero_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).prepZero) t fun t' => Ctx L g m₀ t' ∧
      (∀ r, r ≠ .rcx → t'.gpr r = t.gpr r) ∧
      Frame [⟨L.B + BitVec.ofNat 64 240, 8 * nz P⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 240) (8 * nz P) = List.replicate (8 * nz P) 0 := by
  have hnz : nz P ≤ 18 := by simp only [nz]; split <;> omega
  rw [Cfg.prepZero, WP.block_append_iff]
  have h₁ : WP isa (.block [.alu32 .xor .rcx (.reg .rcx)]) t fun u => Ctx L g m₀ u ∧ u.rd = t.rd ∧
      u.wr = t.wr ∧ u.mem = t.mem ∧ u.gpr .rcx = 0 ∧ ∀ r, r ≠ .rcx → u.gpr r = t.gpr r := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, State.setReg32,
      Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true,
      Option.some.injEq, exists_eq_left', xor_self_zx]
    exact ⟨hc.regs hL rfl rfl rfl rfl (by cs_tac), by triv, by triv, by triv, by triv, fun r hr => by simp [hr]⟩
  have e : (if (cfgOf P).wide then 18 else 9) = nz P := rfl
  rw [e]
  refine WP.mono h₁ fun u ⟨hcu, hrd, hwr, hm, hcx, hg⟩ => ?_
  refine WP.mono_syms (zeroY_ok hcu (nz P) hnz u rfl rfl hcx) fun u' ⟨hrd', hwr', hg', hf', hz'⟩ hsy => ?_
  have hc' : Ctx L g m₀ u' := hcu.keep hL hrd' hwr' (by rw [hg']) (fun r _ _ => by rw [hg']) hf'
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact safe_high L (by omega) (by simp only [nz]; split <;> omega)) hsy
  exact ⟨hc', fun r hr => by rw [hg', hg r hr], by rw [← hm]; exact hf', by
    rw [bytesAt_of_readW _ _ 0 hz', zeros_bytes]⟩

/-- `d ← d - r`. -/
theorem subReg_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved) (r : Reg) :
    WP isa (.block [.alu .sub d (.reg r)]) u (Upd L g m₀ u d (u.gpr d - u.gpr r)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨hc.set hL hd rfl rfl rfl rfl fun r hr => ?_, rfl, RegUpd.gpr_setReg_self _ _ _, fun r hr => ?_⟩
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- `rcx ← min rcx rax`, by a comparison and a conditional move. -/
theorem minQ_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {D Q : Nat} (hD : D < 2 ^ 64) (hQ : Q < 2 ^ 64)
    (hcx : u.gpr .rcx = BitVec.ofNat 64 D) (hax : u.gpr .rax = BitVec.ofNat 64 Q) :
    WP isa (.block [.alu .cmp .rcx (.reg .rax), .cmov .ae .rcx (.reg .rax)]) u
      (Upd L g m₀ u .rcx (BitVec.ofNat 64 (min D Q))) := by
  have hlt : decide ((BitVec.ofNat 64 D).toNat < (BitVec.ofNat 64 Q).toNat) = decide (D < Q) := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hD, Nat.mod_eq_of_lt hQ]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execCmov, readSrc, eval,
    Option.bind_some, Option.map_some, RegUpd.cf_arithFlags, RegUpd.gpr_arithFlags, hcx, hax, hlt,
    Option.some.injEq, exists_eq_left']
  by_cases h : D < Q
  · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, Nat.min_eq_left (Nat.le_of_lt h)]
    exact ⟨hc.set hL (d := .rcx) (by decide) rfl rfl rfl rfl fun r _ => by rw [RegUpd.gpr_arithFlags], rfl,
      by rw [RegUpd.gpr_arithFlags, hcx], fun r _ => by rw [RegUpd.gpr_arithFlags]⟩
  · simp only [h, decide_false, Bool.not_false, ite_true, Nat.min_eq_right (Nat.le_of_not_lt h)]
    exact ⟨hc.set hL (d := .rcx) (by decide) rfl rfl rfl rfl fun r hr => by
        rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags], rfl, RegUpd.gpr_setReg_self _ _ _,
      fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]⟩

/-- `X`, the `Q`-byte number `bits2int` takes of a digest `dg`, for a curve
whose `nBits` is `8 Q`: its leftmost `Q` bytes, or it after `Q - D` zero
bytes if it is shorter. -/
def xOfDg (Q : Nat) (dg : List Byte) : List Byte :=
  List.replicate (Q - min dg.length Q) 0 ++ dg.take Q

/-- A dispatch on the hash function: the case of `P`'s, from a state of other flags. -/
theorem dispatch_ok (P : RfcHash) {f : Impl.Pbkdf2.Md.X86_64.Hash → Prog isa} {s : State}
    {Q : State → Prop} (hs : s.gpr .rax = BitVec.ofNat 64 P.k)
    (h : ∀ s', Proof.Dispatch.X86_64.FlagsOnly s s' → WP isa (f P.H) s' Q) :
    WP isa (Impl.Dispatch.X86_64.chain ((cfgOf P).hs.map fun p => (p.1, f p.2))) s Q := by
  have hk := P.hk
  have hk8 : P.k < 8 := by
    simp only [Spec.Ecdsa.Rfc6979.hashIds, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
  have hsel : Proof.Dispatch.X86_64.sel s = P.k := by
    rw [Proof.Dispatch.X86_64.sel, hs, BitVec.toNat_ofNat]; omega
  have hkeys := keys_cases P f
  refine Proof.Dispatch.chain_wp Proof.Dispatch.X86_64.tests _ ?_ ?_ ?_ fun c hc s' hr _ => ?_
  · intro i hi
    rw [Proof.Dispatch.keys, hkeys] at hi
    simp only [Spec.Ecdsa.Rfc6979.hashIds, List.mem_cons, List.not_mem_nil, or_false] at hi; omega
  · rw [Proof.Dispatch.keys, hkeys, hsel]; exact hk
  · rw [Proof.Dispatch.keys, hkeys]; decide
  · rw [hsel] at hc
    rw [case_eq P f hc]
    exact h s' hr

/-- Bytes within a run of zero bytes. -/
theorem zeros_sub {m : Mem} {p : Addr} {N : Nat} (hz : Spec.Sha256.bytesAt m p N = List.replicate N 0) {a n : Nat}
    (h : a + n ≤ N) : Spec.Sha256.bytesAt m (p + BitVec.ofNat 64 a) n = List.replicate n 0 := by
  have e := bytesAt_take m p h
  rw [hz, List.take_replicate, Nat.min_eq_left h, Proof.Hmac.Common.bytesAt_add, ← List.replicate_append_replicate] at e
  exact (List.append_inj e (by simp [Spec.Sha256.bytesAt])).2

/-- The digest's `m` leftmost bytes to the frame, ending at `rsp + e`, by a
loop, for `m` (a multiple of 4) in `rcx` after `copyLen`. -/
theorem copyDg_ok (hL : L.Ok) {t : State} (hsi : t.gpr .rsi = L.dg) {e m : Nat}
    (hlen : WP isa (.block (cfgOf P).copyLen) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧
      u.gpr .rcx = BitVec.ofNat 64 m ∧ ∀ r, r ≠ .rax → r ≠ .rcx → u.gpr r = t.gpr r)
    (hm4 : m % 4 = 0) (hm0 : 0 < m) (hmD : m ≤ dn) (hm64 : m ≤ 64) (he₁ : 216 + m ≤ e) (he₂ : 24 + e ≤ 520) :
    WP isa ((cfgOf P).copyDg e) t fun t' => Ctx L g m₀ t' ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → t'.gpr r = t.gpr r) ∧
      Frame [⟨L.B + BitVec.ofNat 64 (24 + e - m), m⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (24 + e - m)) m = Spec.Sha256.bytesAt t.mem L.dg m := by
  have he := L.he
  have hm : 4 * (m / 4) = m := by omega
  rw [Cfg.copyDg]
  have hblk : WP isa (.block ((cfgOf P).copyLen ++ Cfg.copyDst e)) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧
      u.gpr .rcx = BitVec.ofNat 64 m ∧ u.gpr .rdx = L.B + BitVec.ofNat 64 (24 + e - m) ∧
      ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → u.gpr r = t.gpr r := by
    rw [WP.block_append_iff]
    refine WP.mono hlen fun u ⟨hcu, hmu, hcx, hg⟩ => ?_
    rw [show Cfg.copyDst e = Cfg.fr .rdx e ++ [.alu .sub .rdx (.reg .rcx)] from rfl, WP.block_append_iff]
    refine WP.mono (fr_ok hL hcu (d := .rdx) (by decide) (o := e) (by omega)) fun u₁ h₁ => ?_
    refine WP.mono (subReg_ok hL h₁.ctx (d := .rdx) (by decide) .rcx) fun u₂ h₂ => ?_
    refine ⟨h₂.ctx, by rw [h₂.mem, h₁.mem, hmu], by rw [h₂.keep _ (by decide), h₁.keep _ (by decide), hcx], ?_,
      fun r h₁' h₂' h₃' => by rw [h₂.keep _ h₃', h₁.keep _ h₃', hg r h₁' h₂']⟩
    rw [h₂.val, h₁.val, h₁.keep _ (by decide), hcx, Offset.add_ofNat_sub _ (by omega)]
  refine WP.seq (WP.mono hblk fun u ⟨hcu, hmu, hcx, hdx, hg⟩ => ?_)
  have hsiu : u.gpr .rsi = L.dg := (hg _ (by decide) (by decide) (by decide)).trans hsi
  have hsep : Region.Disjoint ⟨L.dg, 4 * (m / 4)⟩ ⟨L.B + BitVec.ofNat 64 (24 + e - m), 4 * (m / 4)⟩ := by
    rw [hm]; exact (hL.stk_DG (by omega)).symm.sub_left (Region.sub_prefix hmD)
  refine WP.mono_syms (copyLoop_ok (n := m / 4) (by omega) (by omega) hsep (by have := hL.ng; omega)
    (by rw [hcx, hm]) hsiu hdx (fun i hi => hcu.inDg (by omega) (by omega))
    (fun i hi => by rw [Offset.add_add]; exact hcu.inFrW (by omega) (by omega)))
    fun u' ⟨hrd, hwr, hg', hsy', hf, hb⟩ hsy => ?_
  rw [hm] at hf hb
  refine ⟨hcu.keep hL hrd hwr (hg' _ (by decide) (by decide)) (fun r hr _ => hg' r (ne_cs hr (by decide))
      (ne_cs hr (by decide))) hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega) (by omega)) hsy,
    fun r h₁ h₂ h₃ => (hg' r h₁ h₂).trans (hg r h₁ h₂ h₃), by rw [← hmu]; exact hf, by rw [hb, hmu]⟩

/-- `copyLen`, unless `wide`: `min D Q` in `rcx`. -/
theorem copyLenA_ok (hL : L.Ok) (hq : HashLay P L) (hA : P.R.wide = false) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).copyLen) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧
      u.gpr .rcx = BitVec.ofNat 64 (min P.H.D P.Q) ∧ ∀ r, r ≠ .rax → r ≠ .rcx → u.gpr r = t.gpr r := by
  have e : (cfgOf P).copyLen = [.mov .rcx (.mem (stk fHL))] ++ [.mov32 .rax (.imm (BitVec.ofNat 32 P.Q))] ++
      [.alu .cmp .rcx (.reg .rax), .cmov .ae .rcx (.reg .rax)] := by
    simp only [Cfg.copyLen, cfgOf, hA, Bool.false_eq_true, ite_false]; rfl
  rw [e, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldHL_ok hL hq hc (d := .rcx) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (mov32_ok hL h₁.ctx (d := .rax) (by decide) (n := P.Q) (by nums)) fun u₂ h₂ => ?_
  refine WP.mono (minQ_ok hL h₂.ctx (D := P.H.D) (Q := P.Q) (by nums) (by nums)
    (by rw [h₂.keep _ (by decide), h₁.val]) h₂.val) fun u₃ h₃ => ?_
  exact ⟨h₃.ctx, by rw [h₃.mem, h₂.mem, h₁.mem], h₃.val, fun r hr₁ hr₂ => by
    rw [h₃.keep _ hr₂, h₂.keep _ hr₁, h₁.keep _ hr₂]⟩

/-- `copyLen`, if `wide`: `D` in `rcx`. -/
theorem copyLenW_ok (hL : L.Ok) (hq : HashLay P L) (hW : P.R.wide = true) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).copyLen) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧
      u.gpr .rcx = BitVec.ofNat 64 P.H.D ∧ ∀ r, r ≠ .rax → r ≠ .rcx → u.gpr r = t.gpr r := by
  have e : (cfgOf P).copyLen = [.mov .rcx (.mem (stk fHL))] := by
    simp only [Cfg.copyLen, cfgOf, hW, ite_true]
  rw [e]
  exact WP.mono (ldHL_ok hL hq hc (d := .rcx) (by decide)) fun u h =>
    ⟨h.ctx, h.mem, h.val, fun r _ hr => h.keep r hr⟩

/-- The digest's copy, unless `wide`: `Y`'s `Q` bytes are `X`. -/
theorem prepCopyA_ok (hL : L.Ok) (hq : HashLay P L) (hA : P.R.wide = false) {t : State} (hc : Ctx L g m₀ t)
    (hdn : P.H.D ≤ dn) (hsi : t.gpr .rsi = L.dg)
    (hz : Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 240) 72 = List.replicate 72 0) :
    WP isa (cfgOf P).prepCopy t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 240, 72⟩] t.mem t'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → t'.gpr r = t.gpr r) ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 240) P.Q =
        xOfDg P.Q (Spec.Sha256.bytesAt t.mem L.dg P.H.D) := by
  obtain ⟨hQ8, h8, hQ64⟩ := P.sizesA hA
  have hD := P.sizes
  have he := L.he
  have hm4 : min P.H.D P.Q % 4 = 0 := by
    rcases hQ8 with h | ⟨-, h | h⟩ <;> rcases P.dims with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ |
      ⟨h', -⟩ <;> simp only [h, h'] <;> omega
  have hl : (Spec.Sha256.bytesAt t.mem L.dg P.H.D).length = P.H.D := by simp [Spec.Sha256.bytesAt]
  have e : (cfgOf P).prepCopy = (cfgOf P).copyDg (fY + P.Q) := by
    simp only [Cfg.prepCopy, cfgOf, hA, Bool.false_eq_true, ite_false]
  rw [e]
  refine WP.mono (copyDg_ok hL hsi (copyLenA_ok hL hq hA hc) hm4 (by nums) (by omega) (by nums)
    (by simp only [fY]; omega) (by simp only [fY]; nums))
    fun u ⟨hcu, hg, hf, hb⟩ => ⟨hcu, hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by simp only [fY]; omega) (by simp only [fY]; nums)⟩,
      hg, ?_⟩
  simp only [fY] at hf hb
  have hsplit := Proof.Hmac.Common.bytesAt_add u.mem (L.B + BitVec.ofNat 64 240) (P.Q - min P.H.D P.Q) (min P.H.D P.Q)
  rw [show P.Q - min P.H.D P.Q + min P.H.D P.Q = P.Q by omega, Offset.add_add,
    show 240 + (P.Q - min P.H.D P.Q) = 24 + (216 + P.Q) - min P.H.D P.Q by omega, hb] at hsplit
  rw [hsplit]
  unfold xOfDg
  have hdg : Spec.Sha256.bytesAt t.mem L.dg (min P.H.D P.Q) = (Spec.Sha256.bytesAt t.mem L.dg P.H.D).take P.Q := by
    by_cases h : P.H.D ≤ P.Q
    · rw [Nat.min_eq_left h, List.take_of_length_le (by rw [hl]; exact h)]
    · rw [Nat.min_eq_right (by omega), ← bytesAt_take _ _ (by omega)]
  rw [hl, hdg]
  refine congrArg (· ++ (Spec.Sha256.bytesAt t.mem L.dg P.H.D).take P.Q) ?_
  rw [bytesAt_frame hf (p := L.B + BitVec.ofNat 64 240) (n := P.Q - min P.H.D P.Q) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by nums)) (by omega)]
  have := zeros_sub hz (a := 0) (n := P.Q - min P.H.D P.Q) (by omega)
  rwa [add_ofNat_zero] at this

/-- The digest's copies, if `wide`: `Y`'s `Q` bytes are the digest between
`Q - D - 1` zero bytes and one, and `h`'s the digest after `Q - D`. -/
theorem prepCopyW_ok (hL : L.Ok) (hq : HashLay P L) (hW : P.R.wide = true) {t : State} (hc : Ctx L g m₀ t)
    (hdn : P.H.D ≤ dn) (hsi : t.gpr .rsi = L.dg)
    (hz : Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 240) 144 = List.replicate 144 0) :
    WP isa (cfgOf P).prepCopy t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 240, 144⟩] t.mem t'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → t'.gpr r = t.gpr r) ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 240) P.Q =
        List.replicate (P.Q - P.H.D - 1) 0 ++ Spec.Sha256.bytesAt t.mem L.dg P.H.D ++ [0] ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 312) P.Q =
        List.replicate (P.Q - P.H.D) 0 ++ Spec.Sha256.bytesAt t.mem L.dg P.H.D := by
  obtain ⟨hw9, hQ66⟩ := P.sizesW hW
  have he := L.he
  have hD64 : P.H.D ≤ 64 := by nums
  have hD20 : 20 ≤ P.H.D := by nums
  have hD4 : P.H.D % 4 = 0 := by nums
  have e : (cfgOf P).prepCopy = .seq ((cfgOf P).copyDg (fY + P.Q - 1)) ((cfgOf P).copyDg (fH + P.Q)) := by
    simp only [Cfg.prepCopy, cfgOf, hW, ite_true]
  rw [e]
  refine WP.seq (WP.mono (copyDg_ok hL hsi (copyLenW_ok hL hq hW hc) hD4 (by omega) hdn hD64
    (by simp only [fY]; omega) (by simp only [fY]; omega)) fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_)
  have hsi₁ : u₁.gpr .rsi = L.dg := (hg₁ _ (by decide) (by decide) (by decide)).trans hsi
  have hdg₁ : Spec.Sha256.bytesAt u₁.mem L.dg P.H.D = Spec.Sha256.bytesAt t.mem L.dg P.H.D :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_DG (by simp only [fY]; omega)).symm.sub_left (Region.sub_prefix hdn)) (by omega)
  refine WP.mono (copyDg_ok hL hsi₁ (copyLenW_ok hL hq hW hc₁) hD4 (by omega) hdn hD64
    (by simp only [fH]; omega) (by simp only [fH]; omega))
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ⟨hc₂, ?_, fun r h₁ h₂ h₃ => (hg₂ r h₁ h₂ h₃).trans (hg₁ r h₁ h₂ h₃), ?_, ?_⟩
  · refine (hf₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by simp only [fY]; omega) (by simp only [fY]; omega)
    · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by simp only [fH]; omega) (by simp only [fH]; omega)
  · -- `Y`: zeros, the digest, a zero.
    simp only [fY] at hf₁ hb₁
    simp only [fH] at hf₂
    have k₂ : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 240) P.Q =
        Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 240) P.Q :=
      bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
    have z₁ : Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 240) (P.Q - P.H.D - 1) =
        List.replicate (P.Q - P.H.D - 1) 0 := by
      rw [bytesAt_frame hf₁ (p := L.B + BitVec.ofNat 64 240) (n := P.Q - P.H.D - 1) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)]
      have := zeros_sub hz (a := 0) (n := P.Q - P.H.D - 1) (by omega)
      rwa [add_ofNat_zero] at this
    have z₂ : Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (240 + (P.Q - 1))) 1 = [0] := by
      rw [bytesAt_frame hf₁ (p := L.B + BitVec.ofNat 64 (240 + (P.Q - 1))) (n := 1) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)]
      have := zeros_sub hz (a := P.Q - 1) (n := 1) (by omega)
      rwa [Offset.add_add] at this
    rw [k₂, show P.Q = (P.Q - P.H.D - 1) + P.H.D + 1 by omega, Proof.Hmac.Common.bytesAt_add,
      Proof.Hmac.Common.bytesAt_add, Offset.add_add, Offset.add_add,
      show (P.Q - P.H.D - 1) + P.H.D + 1 - P.H.D - 1 = P.Q - P.H.D - 1 by omega,
      show 240 + (P.Q - P.H.D - 1) = 24 + (216 + P.Q - 1) - P.H.D by omega, hb₁,
      show 240 + (P.Q - P.H.D - 1 + P.H.D) = 240 + (P.Q - 1) by omega, z₁, z₂]
  · -- `h`: zeros, the digest.
    simp only [fY] at hf₁
    simp only [fH] at hf₂ hb₂
    rw [show P.Q = (P.Q - P.H.D) + P.H.D by omega, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
      show 312 + (P.Q - P.H.D) = 24 + (288 + P.Q) - P.H.D by omega, hb₂, hdg₁,
      show (P.Q - P.H.D) + P.H.D - P.H.D = P.Q - P.H.D by omega]
    refine congrArg (· ++ Spec.Sha256.bytesAt t.mem L.dg P.H.D) ?_
    rw [bytesAt_frame hf₂ (p := L.B + BitVec.ofNat 64 312) (n := P.Q - P.H.D) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega),
      bytesAt_frame hf₁ (p := L.B + BitVec.ofNat 64 312) (n := P.Q - P.H.D) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)]
    have := zeros_sub hz (a := 72) (n := P.Q - P.H.D) (by omega)
    rwa [Offset.add_add] at this

end VG.Proof.Ecdsa.Rfc6979.X86_64
