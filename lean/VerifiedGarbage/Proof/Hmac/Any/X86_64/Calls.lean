module

public import VerifiedGarbage.Proof.Hmac.Any.X86_64.Verified
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega

/-!
# HMAC and streaming `update` with the hash function as an argument on x86-64: their calls

For a caller of `vg_hmac_init_scratch`, `vg_hash_update_scratch` and
`vg_hmac_finalize_scratch` of a tier `t`: each call, with its arguments in
registers (`InitA`, `UpdA`, `FinA`), is run with `WP.call` (`init_call`,
`upd_call`, `fin_call`) and shown constant time in two runs with the same
public arguments with `RelCT.call` (`init_rel`, `upd_rel`, `fin_rel`), as
`Proof/Pbkdf2/Md/X86_64/PbkCalls.lean` does for one hash function's. Each
call uses at most 32 bytes of stack below `rsp`.
-/

@[expose] public section

namespace VG.Proof.Hmac.Any.X86_64

open VG.X86_64
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Hmac.Any (inst hashIds)
open Spec.Sha256 (bytesAt)
open VG.Impl.Hmac.Any.X86_64 (ldSel)
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash Tier core_hmacInit core_hmacFin core_updC core_hmacInit_depth
  core_hmacFin_depth nosp_of)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (ne_rsp)
open VG.Proof.Pbkdf2.Md.X86_64.Pbk (covers_app)

variable (t : Tier)

/-! ## The code's shape -/

theorem ldSel_ns : NoSp (Code.block ldSel : Prog isa) := by decide

theorem test_ns (k : Nat) : (Code.block (Impl.Dispatch.X86_64.test k) : Prog isa).allInstrs
    (fun i => !Taint.clobbers i .rsp) = true := rfl

theorem init_ns : NoSp (Impl.Hmac.Any.X86_64.init (hsOf (vsOf t))) := by
  refine nosp_of ?_
  show ((Code.block ldSel : Prog isa).allInstrs _ && (Impl.Dispatch.X86_64.chain _).allInstrs _) = true
  rw [show (Code.block ldSel : Prog isa).allInstrs (fun i => !Taint.clobbers i .rsp) = true by decide,
    Bool.true_and]
  refine Proof.Dispatch.chain_allInstrs (M := isa) _ test_ns _ fun c hc => ?_
  obtain ⟨v, -, e⟩ := mem_map (k := c.1) (c := c.2) (fun _ => rfl) hc
  rw [← show (c.1, Code.call v.H.hmacInitN v.H.hmacInit).2 = c.2 from congrArg Prod.snd e]
  exact core_hmacInit v.K.cNs v.K.iNs v.C.hinitNs

theorem upd_ns : NoSp (Impl.Hmac.Any.X86_64.update (hsOf (vsOf t))) := by
  refine nosp_of ?_
  show ((Code.block ldSel : Prog isa).allInstrs _ && (Impl.Dispatch.X86_64.chain _).allInstrs _) = true
  rw [show (Code.block ldSel : Prog isa).allInstrs (fun i => !Taint.clobbers i .rsp) = true by decide,
    Bool.true_and]
  refine Proof.Dispatch.chain_allInstrs (M := isa) _ test_ns _ fun c hc => ?_
  obtain ⟨v, -, e⟩ := mem_map (k := c.1) (c := c.2) (fun _ => rfl) hc
  rw [← show (c.1, Code.call v.H.updN v.H.updC).2 = c.2 from congrArg Prod.snd e]
  exact core_updC v.K.cNs v.C.updNs

theorem fin_ns : NoSp (Impl.Hmac.Any.X86_64.finalize (hsOf (vsOf t))) := by
  refine nosp_of ?_
  show ((Code.block ldSel : Prog isa).allInstrs _ && (Impl.Dispatch.X86_64.chain _).allInstrs _) = true
  rw [show (Code.block ldSel : Prog isa).allInstrs (fun i => !Taint.clobbers i .rsp) = true by decide,
    Bool.true_and]
  refine Proof.Dispatch.chain_allInstrs (M := isa) _ test_ns _ fun c hc => ?_
  obtain ⟨v, -, e⟩ := mem_map (k := c.1) (c := c.2) (fun _ => rfl) hc
  rw [← show (c.1, Code.call v.H.hmacFinN v.H.hmacFin).2 = c.2 from congrArg Prod.snd e]
  exact core_hmacFin v.K.cNs v.C.hfinNs

theorem init_depth : (Impl.Hmac.Any.X86_64.init (hsOf (vsOf t))).depth ≤ 3 := by
  show max 0 (Impl.Dispatch.X86_64.chain _).depth ≤ 3
  refine Nat.max_le.mpr ⟨Nat.zero_le _, Proof.Dispatch.X86_64.chain_depth _ fun c hc => ?_⟩
  obtain ⟨v, -, e⟩ := mem_map (k := c.1) (c := c.2) (fun _ => rfl) hc
  rw [← show (c.1, Code.call v.H.hmacInitN v.H.hmacInit).2 = c.2 from congrArg Prod.snd e]
  show v.H.hmacInit.depth + 1 ≤ 3
  have := core_hmacInit_depth v.K.cD v.K.iD v.C.hinitD
  omega

theorem upd_depth : (Impl.Hmac.Any.X86_64.update (hsOf (vsOf t))).depth ≤ 2 := by
  show max 0 (Impl.Dispatch.X86_64.chain _).depth ≤ 2
  refine Nat.max_le.mpr ⟨Nat.zero_le _, Proof.Dispatch.X86_64.chain_depth _ fun c hc => ?_⟩
  obtain ⟨v, -, e⟩ := mem_map (k := c.1) (c := c.2) (fun _ => rfl) hc
  rw [← show (c.1, Code.call v.H.updN v.H.updC).2 = c.2 from congrArg Prod.snd e]
  show v.H.updC.depth + 1 ≤ 2
  have := v.K.updD v.C
  omega

theorem fin_depth : (Impl.Hmac.Any.X86_64.finalize (hsOf (vsOf t))).depth ≤ 3 := by
  show max 0 (Impl.Dispatch.X86_64.chain _).depth ≤ 3
  refine Nat.max_le.mpr ⟨Nat.zero_le _, Proof.Dispatch.X86_64.chain_depth _ fun c hc => ?_⟩
  obtain ⟨v, -, e⟩ := mem_map (k := c.1) (c := c.2) (fun _ => rfl) hc
  rw [← show (c.1, Code.call v.H.hmacFinN v.H.hmacFin).2 = c.2 from congrArg Prod.snd e]
  show v.H.hmacFin.depth + 1 ≤ 3
  have := core_hmacFin_depth v.K.cD v.C.hfinD
  omega

/-! ## The stack below a call -/

theorem ret32 (s : State) : Region.Sub ⟨s.callEntry.gpr .rsp, 8⟩ (below (s.gpr .rsp) 32) := by
  rw [State.callEntry_rsp]; exact Offset.sub_below _ (a := 8) (by omega) (by omega)

theorem stk32 (s : State) : Region.Sub ⟨s.callEntry.gpr .rsp - 24, 24⟩ (below (s.gpr .rsp) 32) := by
  rw [State.callEntry_rsp, show s.gpr .rsp - 8 - 24 = s.gpr .rsp - BitVec.ofNat 64 32 from
    Offset.sub_sub_ofNat _ 8 24]
  exact Offset.sub_below _ (a := 32) (by omega) (by omega)

theorem ret24 (s : State) : Region.Sub ⟨s.callEntry.gpr .rsp, 8⟩ (below (s.gpr .rsp) 24) := by
  rw [State.callEntry_rsp]; exact Offset.sub_below _ (a := 8) (by omega) (by omega)

theorem stk24 (s : State) : Region.Sub ⟨s.callEntry.gpr .rsp - 16, 16⟩ (below (s.gpr .rsp) 24) := by
  rw [State.callEntry_rsp, show s.gpr .rsp - 8 - 16 = s.gpr .rsp - BitVec.ofNat 64 24 from
    Offset.sub_sub_ofNat _ 8 16]
  exact Offset.sub_below _ (a := 24) (by omega) (by omega)

/-- Bytes outside the stack below `rsp` read the same on entry to a callee. -/
theorem entry_bytes {n : Nat} (hn : 8 ≤ n) (hn' : n < 2 ^ 63) (s : State) {p : Addr} {len : Nat}
    (hd : (below (s.gpr .rsp) n).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    bytesAt s.callEntry.mem p len = bytesAt s.mem p len := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => Proof.Sha256.X86_64.Stream.callEntry_byte s (R := ⟨p, len⟩)
    (hd.sub_left (below_sub hn (by omega))) hl (List.mem_range.mp hi)

/-- The hash function `k` names in the tier `t`, of the instance `I`. -/
theorem inst_v {k : Nat} (hk : k ∈ hashIds) {I : Spec.Hmac.Instance} (hI : inst k = some I) :
    ∃ v, (k, v) ∈ vsOf t ∧ v.I = I := by
  have G := good t
  have hk' : k ∈ (vsOf t).map (·.1) := by rw [G.keys]; exact hk
  obtain ⟨⟨k', v⟩, hm, rfl⟩ := List.mem_map.mp hk'
  refine ⟨v, hm, ?_⟩
  rw [G.inst _ v hm] at hI
  exact Option.some.inj hI

include t in
/-- A streaming state of `I` outside the stack below `rsp` represents the
same message on entry to a callee. -/
theorem entry_repr {n : Nat} (hn : 8 ≤ n) (hn' : n < 2 ^ 63) (s : State) {k : Nat} (hk : k ∈ hashIds)
    {I : Spec.Hmac.Instance} (hI : inst k = some I) {p : Addr}
    (hd : (below (s.gpr .rsp) n).Disjoint ⟨p, 192⟩) {m : List Byte} (h : I.S.Repr s.mem p m) :
    I.S.Repr s.callEntry.mem p m := by
  obtain ⟨v, hm, rfl⟩ := inst_v t hk hI
  obtain ⟨-, hS192, -, -, -, -⟩ := sizes (good t) hm
  rw [← v.hSH] at h ⊢
  refine v.ok.sh_reloc _ _ _ _ _ (fun i hi => ?_) h
  exact Proof.Sha256.X86_64.Stream.callEntry_byte s (R := ⟨p, 192⟩)
    (hd.sub_left (below_sub hn (by omega))) (by show (192 : Nat) ≤ 2 ^ 64; decide)
    (by show i < 192; have : i < v.H.S := hi; omega)

/-! ## `init` -/

/-- The arguments of a call of `vg_hmac_init_scratch`. -/
structure InitA (s : State) (inn out k sc : Addr) (kl sel : Nat) : Prop where
  rdi : s.gpr .rdi = inn
  rsi : s.gpr .rsi = out
  rdx : s.gpr .rdx = k
  rcx : (s.gpr .rcx).toNat = kl
  r8 : s.gpr .r8 = sc
  r9 : (s.gpr .r9).toNat = sel
  hsel : sel ∈ hashIds
  klB : ∀ I, inst sel = some I → kl ≤ I.S.H.blockSize
  cr : Covers [⟨k, kl⟩] (s.rd ++ s.wr)
  cw : Covers [⟨inn, 192⟩, ⟨out, 192⟩, ⟨sc, 8 * 234⟩] s.wr
  i_o : Region.Disjoint ⟨inn, 192⟩ ⟨out, 192⟩
  i_s : Region.Disjoint ⟨inn, 192⟩ ⟨sc, 8 * 234⟩
  o_s : Region.Disjoint ⟨out, 192⟩ ⟨sc, 8 * 234⟩
  k_i : Region.Disjoint ⟨k, kl⟩ ⟨inn, 192⟩
  k_o : Region.Disjoint ⟨k, kl⟩ ⟨out, 192⟩
  k_s : Region.Disjoint ⟨k, kl⟩ ⟨sc, 8 * 234⟩
  stk_i : (below (s.gpr .rsp) 32).Disjoint ⟨inn, 192⟩
  stk_o : (below (s.gpr .rsp) 32).Disjoint ⟨out, 192⟩
  stk_k : (below (s.gpr .rsp) 32).Disjoint ⟨k, kl⟩
  stk_s : (below (s.gpr .rsp) 32).Disjoint ⟨sc, 8 * 234⟩
  scnw : sc.toNat + 8 * 234 ≤ 2 ^ 64

theorem InitA.pre {s : State} {inn out k sc : Addr} {kl sel : Nat} (a : InitA s inn out k sc kl sel) :
    initA.pre (s.callEntry.withRegions [⟨k, kl⟩] [⟨inn, 192⟩, ⟨out, 192⟩, ⟨sc, 8 * 234⟩]) := by
  simp only [initA, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ne_rsp (by decide : Reg.rdi ≠ .rsp), ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r8 ≠ .rsp), ne_rsp (by decide : Reg.r9 ≠ .rsp),
    a.rdi, a.rsi, a.rdx, a.rcx, a.r8, a.r9]
  exact ⟨⟨a.hsel, a.klB⟩, trivial, trivial, a.i_o, a.i_s, a.o_s, a.k_i, a.k_o, a.k_s,
    a.stk_i.sub_left (ret32 s), a.stk_o.sub_left (ret32 s), a.stk_s.sub_left (ret32 s),
    a.stk_i.sub_left (stk32 s), a.stk_o.sub_left (stk32 s), a.stk_k.sub_left (stk32 s),
    a.stk_s.sub_left (stk32 s), a.scnw⟩

theorem init_call {n : String} {s : State} {inn out k sc : Addr} {kl sel : Nat}
    (a : InitA s inn out k sc kl sel) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨inn, 192⟩, ⟨out, 192⟩, ⟨sc, 8 * 234⟩] ++ [below (s.gpr .rsp) 32]) s.mem s'.mem →
      (∀ I, inst sel = some I →
        I.S.Repr s'.mem inn (xorPad (blockKey I.S.H (bytesAt s.mem k kl)) ipad) ∧
        I.S.Repr s'.mem out (xorPad (blockKey I.S.H (bytesAt s.mem k kl)) opad)) → Q s') :
    WP isa (.call n (Impl.Hmac.Any.X86_64.init (hsOf (vsOf t)))) s Q := by
  refine WP.call (init_verified (good t)).1 (init_ns t) (by have := init_depth t; omega) a.pre
    (covers_app a.cr a.cw) a.cw ?_
  intro s' h₁ h₂ h₃ h₄ _ ⟨s₂, hm, _, hpost⟩
  have e : bytesAt s.callEntry.mem k kl = bytesAt s.mem k kl :=
    entry_bytes (by omega) (by omega) s a.stk_k (by have := (BitVec.isLt (s.gpr .rcx)); rw [a.rcx] at this; omega)
  simp only [initA, State.withRegions_gpr, State.withRegions_mem, ne_rsp (by decide : Reg.rdi ≠ .rsp),
    ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r9 ≠ .rsp), a.rdi, a.rsi, a.rdx, a.rcx,
    a.r9, hm, e] at hpost
  exact hQ s' h₁ h₂ h₃ (Frame.below_mono h₄ (by have := init_depth t; omega) (by omega)) hpost

theorem init_rel {n : String} {P : State → State → Prop} {inn out k sc : Addr} {kl sel : Nat}
    (h : ∀ s s', P s s' → InitA s inn out k sc kl sel ∧ InitA s' inn out k sc kl sel ∧
      s.gpr .rsp = s'.gpr .rsp) :
    RelCT isa P (.call n (Impl.Hmac.Any.X86_64.init (hsOf (vsOf t)))) fun _ _ => True := by
  refine RelCT.call (init_verified (good t)).1 (init_verified (good t)).2.1 [⟨k, kl⟩]
    [⟨inn, 192⟩, ⟨out, 192⟩, ⟨sc, 8 * 234⟩] fun s s' hp => ?_
  obtain ⟨a, a', sp⟩ := h s s' hp
  have cx : s.gpr .rcx = s'.gpr .rcx := BitVec.eq_of_toNat_eq (by rw [a.rcx, a'.rcx])
  have c9 : s.gpr .r9 = s'.gpr .r9 := BitVec.eq_of_toNat_eq (by rw [a.r9, a'.r9])
  refine ⟨a.pre, a'.pre, ?_, covers_app a.cr a.cw, a.cw, covers_app a'.cr a'.cw, a'.cw, sp⟩
  simp only [initA, State.withRegions_gpr, State.callEntry_rsp, ne_rsp (by decide : Reg.rdi ≠ .rsp),
    ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r8 ≠ .rsp), ne_rsp (by decide : Reg.r9 ≠ .rsp),
    a.rdi, a'.rdi, a.rsi, a'.rsi, a.rdx, a'.rdx, a.r8, a'.r8, cx, c9, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `update` -/

/-- The arguments of a call of `vg_hash_update_scratch`. -/
structure UpdA (s : State) (st : Addr) (cnt : BitVec 64) (d sc : Addr) (len sel : Nat) : Prop where
  rdi : s.gpr .rdi = st
  rsi : s.gpr .rsi = cnt
  rdx : s.gpr .rdx = d
  rcx : (s.gpr .rcx).toNat = len
  r8 : s.gpr .r8 = sc
  r9 : (s.gpr .r9).toNat = sel
  hsel : sel ∈ hashIds
  cd : Covers [⟨d, len⟩] (s.rd ++ s.wr)
  cw : Covers [⟨st, 192⟩, ⟨sc, 8 * 234⟩] s.wr
  st_sc : Region.Disjoint ⟨st, 192⟩ ⟨sc, 8 * 234⟩
  d_st : Region.Disjoint ⟨d, len⟩ ⟨st, 192⟩
  d_sc : Region.Disjoint ⟨d, len⟩ ⟨sc, 8 * 234⟩
  stk_st : (below (s.gpr .rsp) 24).Disjoint ⟨st, 192⟩
  stk_d : (below (s.gpr .rsp) 24).Disjoint ⟨d, len⟩
  stk_sc : (below (s.gpr .rsp) 24).Disjoint ⟨sc, 8 * 234⟩

theorem UpdA.pre {s : State} {st : Addr} {cnt : BitVec 64} {d sc : Addr} {len sel : Nat}
    (a : UpdA s st cnt d sc len sel) :
    updA.pre (s.callEntry.withRegions [⟨d, len⟩] [⟨st, 192⟩, ⟨sc, 8 * 234⟩]) := by
  simp only [updA, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ne_rsp (by decide : Reg.rdi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r8 ≠ .rsp), ne_rsp (by decide : Reg.r9 ≠ .rsp),
    a.rdi, a.rdx, a.rcx, a.r8, a.r9]
  exact ⟨a.hsel, trivial, trivial, a.st_sc, a.d_st, a.d_sc,
    a.stk_st.sub_left (ret24 s), a.stk_sc.sub_left (ret24 s),
    a.stk_st.sub_left (stk24 s), a.stk_d.sub_left (stk24 s), a.stk_sc.sub_left (stk24 s)⟩

theorem upd_call {n : String} {s : State} {st : Addr} {cnt : BitVec 64} {d sc : Addr} {len sel : Nat}
    (a : UpdA s st cnt d sc len sel) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨st, 192⟩, ⟨sc, 8 * 234⟩] ++ [below (s.gpr .rsp) 24]) s.mem s'.mem →
      (∀ I, inst sel = some I → ∀ m, I.S.Repr s.mem st m → cnt = BitVec.ofNat 64 m.length →
        I.S.Repr s'.mem st (m ++ bytesAt s.mem d len)) → Q s') :
    WP isa (.call n (Impl.Hmac.Any.X86_64.update (hsOf (vsOf t)))) s Q := by
  refine WP.call (upd_verified (good t)).1 (upd_ns t) (by have := upd_depth t; omega) a.pre
    (covers_app a.cd a.cw) a.cw ?_
  intro s' h₁ h₂ h₃ h₄ _ ⟨s₂, hm, _, hpost⟩
  have e : bytesAt s.callEntry.mem d len = bytesAt s.mem d len :=
    entry_bytes (by omega) (by omega) s a.stk_d (by have := (BitVec.isLt (s.gpr .rcx)); rw [a.rcx] at this; omega)
  simp only [updA, Spec.Hmac.Any.updatePost, State.withRegions_gpr, State.withRegions_mem,
    ne_rsp (by decide : Reg.rdi ≠ .rsp), ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r9 ≠ .rsp), a.rdi, a.rsi, a.rdx, a.rcx,
    a.r9, hm, e] at hpost
  refine hQ s' h₁ h₂ h₃ (Frame.below_mono h₄ (by have := upd_depth t; omega) (by omega)) fun I hI m hr hc => ?_
  exact hpost I hI m (entry_repr t (by omega) (by omega) s a.hsel hI a.stk_st hr) hc

theorem upd_rel {n : String} {P : State → State → Prop} {st : Addr} {cnt : BitVec 64} {d sc : Addr}
    {len sel : Nat}
    (h : ∀ s s', P s s' → UpdA s st cnt d sc len sel ∧ UpdA s' st cnt d sc len sel ∧
      s.gpr .rsp = s'.gpr .rsp) :
    RelCT isa P (.call n (Impl.Hmac.Any.X86_64.update (hsOf (vsOf t)))) fun _ _ => True := by
  refine RelCT.call (upd_verified (good t)).1 (upd_verified (good t)).2.1 [⟨d, len⟩]
    [⟨st, 192⟩, ⟨sc, 8 * 234⟩] fun s s' hp => ?_
  obtain ⟨a, a', sp⟩ := h s s' hp
  have cx : s.gpr .rcx = s'.gpr .rcx := BitVec.eq_of_toNat_eq (by rw [a.rcx, a'.rcx])
  have c9 : s.gpr .r9 = s'.gpr .r9 := BitVec.eq_of_toNat_eq (by rw [a.r9, a'.r9])
  refine ⟨a.pre, a'.pre, ?_, covers_app a.cd a.cw, a.cw, covers_app a'.cd a'.cw, a'.cw, sp⟩
  simp only [updA, State.withRegions_gpr, State.callEntry_rsp, ne_rsp (by decide : Reg.rdi ≠ .rsp),
    ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r8 ≠ .rsp), ne_rsp (by decide : Reg.r9 ≠ .rsp),
    a.rdi, a'.rdi, a.rsi, a'.rsi, a.rdx, a'.rdx, a.r8, a'.r8, cx, c9, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `finalize` -/

/-- The arguments of a call of `vg_hmac_finalize_scratch`. -/
structure FinA (s : State) (inn outer : Addr) (cnt : BitVec 64) (o sc : Addr) (sel : Nat) : Prop where
  rdi : s.gpr .rdi = inn
  rsi : s.gpr .rsi = outer
  rdx : s.gpr .rdx = cnt
  rcx : s.gpr .rcx = o
  r8 : s.gpr .r8 = sc
  r9 : (s.gpr .r9).toNat = sel
  hsel : sel ∈ hashIds
  cr : Covers [⟨outer, 192⟩] (s.rd ++ s.wr)
  cw : Covers [⟨inn, 192⟩, ⟨o, 64⟩, ⟨sc, 8 * 234⟩] s.wr
  i_u : Region.Disjoint ⟨inn, 192⟩ ⟨outer, 192⟩
  i_o : Region.Disjoint ⟨inn, 192⟩ ⟨o, 64⟩
  i_s : Region.Disjoint ⟨inn, 192⟩ ⟨sc, 8 * 234⟩
  u_o : Region.Disjoint ⟨outer, 192⟩ ⟨o, 64⟩
  u_s : Region.Disjoint ⟨outer, 192⟩ ⟨sc, 8 * 234⟩
  o_s : Region.Disjoint ⟨o, 64⟩ ⟨sc, 8 * 234⟩
  stk_i : (below (s.gpr .rsp) 32).Disjoint ⟨inn, 192⟩
  stk_u : (below (s.gpr .rsp) 32).Disjoint ⟨outer, 192⟩
  stk_o : (below (s.gpr .rsp) 32).Disjoint ⟨o, 64⟩
  stk_s : (below (s.gpr .rsp) 32).Disjoint ⟨sc, 8 * 234⟩
  scnw : sc.toNat + 8 * 234 ≤ 2 ^ 64

theorem FinA.pre {s : State} {inn outer : Addr} {cnt : BitVec 64} {o sc : Addr} {sel : Nat}
    (a : FinA s inn outer cnt o sc sel) :
    finA.pre (s.callEntry.withRegions [⟨outer, 192⟩] [⟨inn, 192⟩, ⟨o, 64⟩, ⟨sc, 8 * 234⟩]) := by
  simp only [finA, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ne_rsp (by decide : Reg.rdi ≠ .rsp), ne_rsp (by decide : Reg.rsi ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r8 ≠ .rsp), ne_rsp (by decide : Reg.r9 ≠ .rsp),
    a.rdi, a.rsi, a.rcx, a.r8, a.r9]
  exact ⟨a.hsel, trivial, trivial, a.i_u, a.i_o, a.i_s, a.u_o, a.u_s, a.o_s,
    a.stk_i.sub_left (ret32 s), a.stk_u.sub_left (ret32 s), a.stk_o.sub_left (ret32 s),
    a.stk_s.sub_left (ret32 s), a.stk_i.sub_left (stk32 s), a.stk_u.sub_left (stk32 s),
    a.stk_o.sub_left (stk32 s), a.stk_s.sub_left (stk32 s), a.scnw⟩

theorem fin_call {n : String} {s : State} {inn outer : Addr} {cnt : BitVec 64} {o sc : Addr} {sel : Nat}
    (a : FinA s inn outer cnt o sc sel) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨inn, 192⟩, ⟨o, 64⟩, ⟨sc, 8 * 234⟩] ++ [below (s.gpr .rsp) 32]) s.mem s'.mem →
      (∀ I, inst sel = some I → ∀ k0 text, k0.length = I.S.H.blockSize → k0.length + text.length < 2 ^ 64 →
        I.S.Repr s.mem inn (xorPad k0 ipad ++ text) → cnt = BitVec.ofNat 64 (I.S.H.blockSize + text.length) →
        I.S.Repr s.mem outer (xorPad k0 opad) →
        bytesAt s'.mem o I.S.digestBytes = hmacBlockKey I.S.H k0 text) → Q s') :
    WP isa (.call n (Impl.Hmac.Any.X86_64.finalize (hsOf (vsOf t)))) s Q := by
  refine WP.call (fin_verified (good t)).1 (fin_ns t) (by have := fin_depth t; omega) a.pre
    (covers_app a.cr a.cw) a.cw ?_
  intro s' h₁ h₂ h₃ h₄ _ ⟨s₂, hm, _, hpost⟩
  simp only [finA, State.withRegions_gpr, State.withRegions_mem, ne_rsp (by decide : Reg.rdi ≠ .rsp),
    ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r9 ≠ .rsp), a.rdi, a.rsi, a.rdx, a.rcx,
    a.r9, hm] at hpost
  refine hQ s' h₁ h₂ h₃ (Frame.below_mono h₄ (by have := fin_depth t; omega) (by omega))
    fun I hI k0 text hk hl hi hc ho => ?_
  exact hpost I hI k0 text hk hl (entry_repr t (by omega) (by omega) s a.hsel hI a.stk_i hi) hc
    (entry_repr t (by omega) (by omega) s a.hsel hI a.stk_u ho)

theorem fin_rel {n : String} {P : State → State → Prop} {inn outer : Addr} {cnt : BitVec 64} {o sc : Addr}
    {sel : Nat}
    (h : ∀ s s', P s s' → FinA s inn outer cnt o sc sel ∧ FinA s' inn outer cnt o sc sel ∧
      s.gpr .rsp = s'.gpr .rsp) :
    RelCT isa P (.call n (Impl.Hmac.Any.X86_64.finalize (hsOf (vsOf t)))) fun _ _ => True := by
  refine RelCT.call (fin_verified (good t)).1 (fin_verified (good t)).2.1 [⟨outer, 192⟩]
    [⟨inn, 192⟩, ⟨o, 64⟩, ⟨sc, 8 * 234⟩] fun s s' hp => ?_
  obtain ⟨a, a', sp⟩ := h s s' hp
  have c9 : s.gpr .r9 = s'.gpr .r9 := BitVec.eq_of_toNat_eq (by rw [a.r9, a'.r9])
  refine ⟨a.pre, a'.pre, ?_, covers_app a.cr a.cw, a.cw, covers_app a'.cr a'.cw, a'.cw, sp⟩
  simp only [finA, State.withRegions_gpr, State.callEntry_rsp, ne_rsp (by decide : Reg.rdi ≠ .rsp),
    ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r8 ≠ .rsp), ne_rsp (by decide : Reg.r9 ≠ .rsp),
    a.rdi, a'.rdi, a.rsi, a'.rsi, a.rdx, a'.rdx, a.rcx, a'.rcx, a.r8, a'.r8, c9, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.Hmac.Any.X86_64
