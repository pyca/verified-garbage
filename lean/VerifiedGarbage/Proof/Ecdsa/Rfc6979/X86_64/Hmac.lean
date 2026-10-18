module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Copy
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Hash
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Pbkdf2.MdKeys

/-!
# Deterministic ECDSA on x86-64: one HMAC

`HMAC_K(data)` (`Cfg.hmac`), for the key `K` (of the hash function's output
length) in the frame and `len` bytes of data in the frame or in `scratch`
above HMAC's working space (`DataOk`), written to the frame at `dst`, for
any hash function `P` the table names.

Each streaming function is called through `r11`, loaded from its slot in
the frame (`ldFn_ok`), as `FnMeets` says of it in the entry the state keeps
`World` of (`Ctx.calls`): `init_ok`, `upd_ok` and `fin_ok`, which change
only the streaming state, the working space, the output and the 24 bytes
below the frame, and keep `Ctx` (`Ctx.after`). `keyed_ok` sets a state to
`init` and `update` with `K ⊕ pad`, from the block `padBlock_ok` writes to
`scratch` a 32-bit word at a time (`padBlk`); `hmac_ok` is the whole
HMAC (`Done`): it changes only the first 2256 bytes of `scratch`, the 24
bytes below the frame, and the 64 at `dst`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Impl.Mgf1.X86_64 (initF updF finF ldFn)
open VG.Proof.HashFns.X86_64 (UArgs FArgs)
open VG.X86_64.CallC (PassesC)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (After)
open VG.WriteBytes (writeBytes writeBytes_append writeBytes_frame)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

/-- `n` bytes at `p + d` end within the address space. -/
theorem add_bound (p : Addr) {d n : Nat} (h : p.toNat + d + n ≤ 2 ^ 64) :
    (p + BitVec.ofNat 64 d).toNat + n ≤ 2 ^ 64 := by
  by_cases hd : p.toNat + d < 2 ^ 64
  · rw [toNat_add_of hd]; omega
  · have := (p + BitVec.ofNat 64 d).isLt; omega

/-! ## Where the data and the output may be -/

/-- Where the data of an `update` may be: in the frame below its pointers,
or in `scratch` above the states and the working space. -/
def UpdOk {dn : Nat} (L : Lay dn) (da : Addr) (len : Nat) : Prop :=
  (∃ o, da = L.B + BitVec.ofNat 64 o ∧ 24 ≤ o ∧ o + len ≤ 208) ∨
    (∃ o, da = L.scr + BitVec.ofNat 64 o ∧ 1760 ≤ o ∧ o + len ≤ 8192)

/-- Where the data of an HMAC may be: in the frame below its pointers, or in
`scratch` above HMAC's working space. -/
def DataOk {dn : Nat} (L : Lay dn) (da : Addr) (len : Nat) : Prop :=
  (∃ o, da = L.B + BitVec.ofNat 64 o ∧ 24 ≤ o ∧ o + len ≤ 208) ∨
    (∃ o, da = L.scr + BitVec.ofNat 64 o ∧ 2256 ≤ o ∧ o + len ≤ 8192)

/-- Where the output of a `finalize` may be: 64 bytes of the frame's `K`
and `V`, or the inner hash's place in `scratch`. -/
def OutOk {dn : Nat} (L : Lay dn) (o : Addr) : Prop :=
  (∃ d, o = L.B + BitVec.ofNat 64 (24 + d) ∧ d + 64 ≤ 128) ∨ o = L.scr + BitVec.ofNat 64 sTmp

theorem DataOk.upd {da : Addr} {len : Nat} (h : DataOk L da len) : UpdOk L da len := by
  rcases h with ⟨o, h₁, h₂, h₃⟩ | ⟨o, h₁, h₂, h₃⟩
  exacts [.inl ⟨o, h₁, h₂, h₃⟩, .inr ⟨o, h₁, by omega, h₃⟩]

namespace UpdOk

variable {da : Addr} {len : Nat}

theorem safe (hd : UpdOk L da len) : Safe L ⟨da, len⟩ := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  exacts [safe_low L h₂, safe_scr L h₂]

theorem low (hd : UpdOk L da len) (hL : L.Ok) : Region.Disjoint ⟨L.B, 24⟩ ⟨da, len⟩ := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact Offset.base_disjoint _ h₁ (by omega)
  · exact hL.low_scr h₂

/-- The data is apart from the states and the working space. -/
theorem work (hd : UpdOk L da len) (hL : L.Ok) {e k : Nat} (h : e + k ≤ 1760) :
    Region.Disjoint ⟨da, len⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact hL.stk_scr (by have := L.he; omega) (by omega)
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem within (hd : UpdOk L da len) :
    ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨da, len⟩ R := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact ⟨L.FR, by simp, within_fr _ h₁ (by omega)⟩
  · exact ⟨L.SCR, by simp, within_off _ h₂⟩

theorem bound (hd : UpdOk L da len) (hL : L.Ok) : da.toNat + len ≤ 2 ^ 64 := by
  have := hL.nb; have := hL.nc; have := L.he
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact add_bound _ (by omega)
  · exact add_bound _ (by omega)

end UpdOk

namespace DataOk

variable {da : Addr} {len : Nat}

/-- The data is apart from HMAC's working space. -/
theorem work (hd : DataOk L da len) (hL : L.Ok) {e k : Nat} (h : e + k ≤ 2256) :
    Region.Disjoint ⟨da, len⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact hL.stk_scr (by have := L.he; omega) (by omega)
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)

/-- The data is apart from the output at `dst`, for data that is not where
the output goes. -/
theorem low (hd : DataOk L da len) (hL : L.Ok) : Region.Disjoint ⟨da, len⟩ ⟨L.B, 24⟩ :=
  (hd.upd.low hL).symm

end DataOk

namespace OutOk

variable {o : Addr}

theorem safe (ho : OutOk L o) : Safe L ⟨o, 64⟩ := by
  rcases ho with ⟨d, rfl, h⟩ | rfl
  exacts [safe_low L (by omega), safe_scr L (by decide)]

theorem within (ho : OutOk L o) : ∃ R ∈ [L.FR, L.OUT, L.SCR], Within ⟨o, 64⟩ R := by
  rcases ho with ⟨d, rfl, h⟩ | rfl
  · exact ⟨L.FR, by simp, within_fr _ (by omega) (by omega)⟩
  · exact ⟨L.SCR, by simp, within_off _ (by decide)⟩

theorem low (ho : OutOk L o) (hL : L.Ok) : Region.Disjoint ⟨L.B, 24⟩ ⟨o, 64⟩ := by
  rcases ho with ⟨d, rfl, h⟩ | rfl
  · exact Offset.base_disjoint _ (by omega) (by omega)
  · exact hL.low_scr (by decide)

/-- The output is apart from the states and the working space. -/
theorem work (ho : OutOk L o) (hL : L.Ok) {e k : Nat} (h : e + k ≤ 1920) :
    Region.Disjoint ⟨o, 64⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ := by
  rcases ho with ⟨d, rfl, h'⟩ | rfl
  · exact hL.stk_scr (by have := L.he; omega) (by omega)
  · exact Offset.disjoint _ (by simp only [sTmp]; omega) (by decide) (by omega)

theorem bound (ho : OutOk L o) (hL : L.Ok) : o.toNat + 64 ≤ 2 ^ 64 := by
  have := hL.nb; have := hL.nc; have := L.he
  rcases ho with ⟨d, rfl, h⟩ | rfl
  · rw [toNat_add_of (by omega)]; omega
  · rw [toNat_add_of (by simp only [sTmp]; omega)]; simp only [sTmp]; omega

end OutOk

/-! ## The calls -/

theorem ea_sp (t : State) (d : Nat) : t.ea (Impl.Mgf1.X86_64.sp d) = t.gpr .rsp + BitVec.ofNat 64 d :=
  ea_stk t d

/-- `r11 ←` the word of the frame at `rsp + o`. -/
theorem ldFn_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {o : Nat} (ho : o + 8 ≤ 240) :
    WP isa (.block (ldFn o)) u (Upd L g m₀ u .r11 (u.mem.readW (L.B + BitVec.ofNat 64 (24 + o)) 64)) := by
  have hin := hc.inFr (d := 24 + o) (by omega) (by have := L.he; omega)
  apply WP.of_runBlock
  simp only [ldFn, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_sp, hc.rsp,
    Offset.add_add, hin, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL (by decide) rfl rfl rfl ⟨rfl, rfl⟩ fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl,
    RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr⟩

/-- After a call of a streaming function that writes only the safe regions
`ws`, of a state keeping `World` of `e`: `Ctx`, and the memory changed only
there and in the 24 bytes below the frame. -/
theorem Ctx.after (hL : L.Ok) {s s' e : State} (hc : Ctx L g m₀ s) {ws : List Region} (hs : ∀ r ∈ ws, Safe L r)
    (A : After s ws s') (hW : World 408 e s) (hW' : World 408 e s') :
    Ctx L g m₀ s' ∧ Frame (ws ++ [⟨L.B, 24⟩]) s.mem s'.mem := by
  have hb : Region.Sub (below (s.gpr .rsp) 16) ⟨L.B, 24⟩ := hc.below_sub (by omega)
  have hs' : ∀ r ∈ ws ++ [below (s.gpr .rsp) 16], Safe L r := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hs r hr
    · rw [List.mem_singleton] at hr; subst hr
      exact .inr (.inr (.inl (hb.trans (Region.sub_prefix (by omega)))))
  refine ⟨hc.keep hL A.rd A.wr (A.cs .rsp (by decide)) (fun r hr _ => A.cs r hr) A.frame hs'
    ⟨hW'.syms.trans hW.syms.symm, hW'.funs.trans hW.funs.symm⟩, A.frame.sub fun r hr => ?_⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact ⟨r, List.mem_append_left _ hr, sub_refl _⟩
  · rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), hb⟩

/-- What a call of a streaming function from `s` passes: the safe regions
`rd` it reads and `wr` it writes, and the stack below `rsp`. -/
theorem Ctx.passes {s e : State} (hc : Ctx L g m₀ s) (hew : e.wr = [L.OUT, L.SCR])
    (hes : e.gpr .rsp = L.B + BitVec.ofNat 64 408) {rd wr : List Region} (hrd : ∀ r ∈ rd, Safe L r)
    (hwr : ∀ r ∈ wr, Safe L r) (hcw : ∀ r ∈ wr, ∃ R ∈ [L.FR, L.OUT, L.SCR], Within r R) :
    PassesC L.cs 408 8 e s rd wr := by
  refine ⟨hc.coversW hcw, by decide, fun r hr x hx => ?_, owned_safe L hew hes hwr,
    owned_safe L hew hes fun r hr => ?_⟩
  · obtain ⟨R, hR, hx'⟩ := owned_safe L hew hes (ws := [r]) (fun q hq => by
      rw [List.mem_singleton] at hq; subst hq; exact hrd _ hr) r (List.mem_singleton_self _) x hx
    refine ⟨R, ?_, hx'⟩
    rcases List.mem_append.mp hR with h | h
    · exact List.mem_append_left _ (List.mem_append_right _ h)
    · exact List.mem_append_right _ h
  · rw [List.mem_singleton] at hr; subst hr
    exact .inr (.inr (.inl ((hc.below_sub (by omega)).trans (Region.sub_prefix (by omega)))))

theorem Ctx.sp16 {s : State} (hL : L.Ok) (hc : Ctx L g m₀ s) : 16 ≤ (s.gpr .rsp).toNat := by
  have := hL.nb; have := L.he
  rw [hc.rsp, toNat_add_of (by omega)]; omega

theorem scr_bound (hL : L.Ok) {a n : Nat} (h : a + n ≤ 8192) : (L.scr + BitVec.ofNat 64 a).toNat + n ≤ 2 ^ 64 :=
  add_bound _ (by have := hL.nc; omega)

theorem Ctx.stk {s : State} (hL : L.Ok) (hc : Ctx L g m₀ s) {a n : Nat} (h : a + n ≤ 8192) :
    (below (s.gpr .rsp) 16).Disjoint ⟨L.scr + BitVec.ofNat 64 a, n⟩ :=
  (hL.low_scr h).sub_left (hc.below_sub (by omega))

/-- The streaming state at `scratch + st` and the working space. -/
abbrev stR (L : Lay dn) (st : Nat) : Region := ⟨L.scr + BitVec.ofNat 64 st, 192⟩
abbrev workR (L : Lay dn) : Region := ⟨L.scr + BitVec.ofNat 64 sWork, 1536⟩

theorem sub_stR {st : Nat} {n : Nat} (h : n ≤ 192) : Region.Sub ⟨L.scr + BitVec.ofNat 64 st, n⟩ (stR L st) :=
  Region.sub_prefix h

theorem sub_workR {n : Nat} (h : n ≤ 1536) : Region.Sub ⟨L.scr + BitVec.ofNat 64 sWork, n⟩ (workR L) :=
  Region.sub_prefix h

theorem hFns {u : State} (hc : Ctx L g m₀ u) :
    ∃ e, World 408 e u ∧ FnsK L.cs e L.T L.fi L.fu L.ff ∧ e.wr = [L.OUT, L.SCR] ∧
      e.gpr .rsp = L.B + BitVec.ofNat 64 408 := by
  obtain ⟨e, hW, hF, -, hew, hes⟩ := hc.calls
  exact ⟨e, hW, hF, hew, hes⟩

/-- What a call of `init` on the state at `scratch + st` passes. -/
theorem Ctx.iPass {u e : State} (hc : Ctx L g m₀ u) (hew : e.wr = [L.OUT, L.SCR])
    (hes : e.gpr .rsp = L.B + BitVec.ofNat 64 408) {st : Nat} (hst : st + 192 ≤ 384) :
    PassesC L.cs 408 8 e u [] [⟨L.scr + BitVec.ofNat 64 st, P.T.S.stateBytes⟩] := by
  have hz := P.sizes
  exact hc.passes hew hes (by simp) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega))
    fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact ⟨L.SCR, by simp, within_off _ (by omega)⟩

/-- The arguments of `update` of the state at `scratch + st` with the `len` bytes at `da`. -/
theorem Ctx.uArgs (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {st : Nat} (hst : st + 192 ≤ 384)
    {da : Addr} {len : Nat} (hd : UpdOk L da len) (hdi : u.gpr .rdi = L.scr + BitVec.ofNat 64 st)
    (hdx : u.gpr .rdx = da) (hcx : u.gpr .rcx = BitVec.ofNat 64 len) (hlen : len < 2 ^ 32)
    (h8 : u.gpr .r8 = L.scr + BitVec.ofNat 64 sWork) :
    UArgs P.T u (L.scr + BitVec.ofNat 64 st) da (L.scr + BitVec.ofNat 64 sWork) len := by
  have hz := P.sizes
  have hsw : sWork = 384 := rfl
  exact { rdi := hdi, rdx := hdx
          rcx := by rw [hcx, BitVec.toNat_ofNat]; omega
          r8 := h8
          st_sc := Offset.disjoint _ (by omega) (by omega) (by omega)
          d_st := hd.work hL (by omega)
          d_sc := hd.work hL (by omega)
          stk_st := hc.stk hL (by omega)
          stk_d := (hd.low hL).sub_left (hc.below_sub (by omega))
          stk_sc := hc.stk hL (by omega)
          bst := scr_bound hL (by omega), bd := hd.bound hL, bsc := scr_bound hL (by omega)
          sp := hc.sp16 hL }

/-- What a call of `update` of the state at `scratch + st` with the `len` bytes at `da` passes. -/
theorem Ctx.uPass {u e : State} (hc : Ctx L g m₀ u) (hew : e.wr = [L.OUT, L.SCR])
    (hes : e.gpr .rsp = L.B + BitVec.ofNat 64 408) {st : Nat} (hst : st + 192 ≤ 384) {da : Addr} {len : Nat}
    (hd : UpdOk L da len) :
    PassesC L.cs 408 8 e u [⟨da, len⟩] [⟨L.scr + BitVec.ofNat 64 st, P.T.S.stateBytes⟩,
      ⟨L.scr + BitVec.ofNat 64 sWork, 8 * P.T.scratch⟩] := by
  have hz := P.sizes
  have hsw : sWork = 384 := rfl
  exact hc.passes hew hes (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd.safe)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact safe_scr L (by omega))
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by omega)⟩

/-- The arguments of `finalize` of the state at `scratch + st` to `o`. -/
theorem Ctx.fArgs (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {st : Nat} (hst : st + 192 ≤ 384)
    {o : Addr} (ho : OutOk L o) (hdi : u.gpr .rdi = L.scr + BitVec.ofNat 64 st) (hdx : u.gpr .rdx = o)
    (hcx : u.gpr .rcx = L.scr + BitVec.ofNat 64 sWork) :
    FArgs P.T u (L.scr + BitVec.ofNat 64 st) o (L.scr + BitVec.ofNat 64 sWork) := by
  have hz := P.sizes
  have hsw : sWork = 384 := rfl
  have hos : Region.Sub ⟨o, P.T.outBytes⟩ ⟨o, 64⟩ := Region.sub_prefix (by omega)
  exact { rdi := hdi, rdx := hdx, rcx := hcx
          st_o := ((ho.work hL (e := st) (k := 192) (by omega)).symm.sub_left
            (Region.sub_prefix (by omega))).sub_right hos
          st_sc := Offset.disjoint _ (by omega) (by omega) (by omega)
          o_sc := (ho.work hL (by omega)).sub_left hos
          stk_st := hc.stk hL (by omega)
          stk_o := ((ho.low hL).sub_left (hc.below_sub (by omega))).sub_right hos
          stk_sc := hc.stk hL (by omega)
          bst := scr_bound hL (by omega), bo := by have := ho.bound hL; omega
          bsc := scr_bound hL (by omega)
          sp := hc.sp16 hL }

/-- What `finalize` writes. -/
theorem fin_safe {o : Addr} (ho : OutOk L o) {st : Nat} (hst : st + 192 ≤ 384) :
    ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 st, P.T.S.stateBytes⟩ : Region), ⟨o, P.T.outBytes⟩,
      ⟨L.scr + BitVec.ofNat 64 sWork, 8 * P.T.scratch⟩], Safe L r := fun r hr => by
  have hz := P.sizes
  have hsw : sWork = 384 := rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact safe_scr L (by omega)
  · exact ho.safe.of_sub (Region.sub_prefix (by omega))
  · exact safe_scr L (by omega)

/-- What a call of `finalize` of the state at `scratch + st` to `o` passes. -/
theorem Ctx.fPass {u e : State} (hc : Ctx L g m₀ u) (hew : e.wr = [L.OUT, L.SCR])
    (hes : e.gpr .rsp = L.B + BitVec.ofNat 64 408) {st : Nat} (hst : st + 192 ≤ 384) {o : Addr} (ho : OutOk L o) :
    PassesC L.cs 408 8 e u [] [⟨L.scr + BitVec.ofNat 64 st, P.T.S.stateBytes⟩, ⟨o, P.T.outBytes⟩,
      ⟨L.scr + BitVec.ofNat 64 sWork, 8 * P.T.scratch⟩] := by
  have hz := P.sizes
  have hsw : sWork = 384 := rfl
  exact hc.passes hew hes (by simp) (fin_safe ho hst) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
    · obtain ⟨R, hR, off, hb, hl⟩ := ho.within
      exact ⟨R, hR, off, hb, by simp only at hl ⊢; omega⟩
    · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩

/-- `init` of the state at `scratch + st`. -/
theorem init_ok (hL : L.Ok) (hT : L.T = P.T) {u : State} (hc : Ctx L g m₀ u) {st : Nat} (hst : st + 192 ≤ 384)
    (hdi : u.gpr .rdi = L.scr + BitVec.ofNat 64 st) :
    WP isa (initF fFn) u fun u' => Ctx L g m₀ u' ∧ Frame [stR L st, ⟨L.B, 24⟩] u.mem u'.mem ∧
      P.T.S.Repr u'.mem (L.scr + BitVec.ofNat 64 st) [] := by
  refine WP.seq (WP.mono (ldFn_ok hL hc (o := fFn) (by decide)) fun u₁ h₁ => ?_)
  obtain ⟨e, hW, hF, hew, hes⟩ := hFns h₁.ctx
  have h11 : u₁.gpr .r11 = L.fi := by rw [h₁.val, ← hc.pFi]; rfl
  have hm := hF.init
  rw [← h11, hT] at hm
  have hz := P.sizes
  have hdi₁ : u₁.gpr .rdi = L.scr + BitVec.ofNat 64 st := (h₁.keep .rdi (by decide)).trans hdi
  have hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 st, P.T.S.stateBytes⟩ : Region)], Safe L r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega)
  refine VG.Proof.HashFns.X86_64.C.init_icall P.T hF.consts hm hW hdi₁ (h₁.ctx.iPass hew hes hst)
    (scr_bound hL (by omega)) (h₁.ctx.sp16 hL) (h₁.ctx.stk hL (by omega)) fun u' A hW' hr => ?_
  obtain ⟨hc', hf⟩ := h₁.ctx.after hL hws A hW hW'
  refine ⟨hc', h₁.mem ▸ hf.sub fun r hr => ?_, hr⟩
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, sub_stR (by omega)⟩
  · rw [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, sub_refl _⟩

/-- `update` of the state at `scratch + st` with the `len` bytes at `da`. -/
theorem upd_ok (hL : L.Ok) (hT : L.T = P.T) {u : State} (hc : Ctx L g m₀ u) {st : Nat} (hst : st + 192 ≤ 384)
    {da : Addr} {len : Nat} (hd : UpdOk L da len) (hdi : u.gpr .rdi = L.scr + BitVec.ofNat 64 st)
    (hdx : u.gpr .rdx = da) (hcx : u.gpr .rcx = BitVec.ofNat 64 len) (hlen : len < 2 ^ 32)
    (h8 : u.gpr .r8 = L.scr + BitVec.ofNat 64 sWork) :
    WP isa (updF fFn) u fun u' => Ctx L g m₀ u' ∧ Frame [stR L st, workR L, ⟨L.B, 24⟩] u.mem u'.mem ∧
      ∀ m, P.T.S.Repr u.mem (L.scr + BitVec.ofNat 64 st) m → u.gpr .rsi = BitVec.ofNat 64 m.length →
        P.T.S.Repr u'.mem (L.scr + BitVec.ofNat 64 st) (m ++ Spec.Sha256.bytesAt u.mem da len) := by
  refine WP.seq (WP.mono (ldFn_ok hL hc (o := fFn + 8) (by decide)) fun u₁ h₁ => ?_)
  obtain ⟨e, hW, hF, hew, hes⟩ := hFns h₁.ctx
  have h11 : u₁.gpr .r11 = L.fu := by rw [h₁.val, ← hc.pFu]; rfl
  have hm := hF.upd
  rw [← h11, hT] at hm
  have hz := P.sizes
  have hsw : sWork = 384 := rfl
  have hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 st, P.T.S.stateBytes⟩ : Region),
      ⟨L.scr + BitVec.ofNat 64 sWork, 8 * P.T.scratch⟩], Safe L r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact safe_scr L (by omega)
  refine VG.Proof.HashFns.X86_64.C.upd_icall P.T hF.consts hm hW (P.ok.choose_spec.2.local_)
    (h₁.ctx.uArgs hL hst hd ((h₁.keep .rdi (by decide)).trans hdi) ((h₁.keep .rdx (by decide)).trans hdx)
      ((h₁.keep .rcx (by decide)).trans hcx) hlen ((h₁.keep .r8 (by decide)).trans h8))
    (h₁.ctx.uPass hew hes hst hd) fun u' A hW' hr => ?_
  obtain ⟨hc', hf⟩ := h₁.ctx.after hL hws A hW hW'
  refine ⟨hc', h₁.mem ▸ hf.sub fun r hr => ?_, fun m hm hsi => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, sub_stR (by omega)⟩
    · exact ⟨_, by simp, sub_workR (by omega)⟩
    · exact ⟨_, by simp, sub_refl _⟩
  · rw [← h₁.mem]
    exact hr m (h₁.mem ▸ hm) ((h₁.keep .rsi (by decide)).trans hsi)

/-- The first `D` of the `outBytes` a `finalize` writes. -/
theorem out_take (m : Mem) (o : Addr) :
    Spec.Sha256.bytesAt m o P.D = (Spec.Sha256.bytesAt m o P.T.outBytes).take P.T.S.digestBytes :=
  bytesAt_take m o (by nums)

/-- `finalize` of the state at `scratch + st` to `o`. -/
theorem fin_ok (hL : L.Ok) (hT : L.T = P.T) {u : State} (hc : Ctx L g m₀ u) {st : Nat} (hst : st + 192 ≤ 384)
    {o : Addr} (ho : OutOk L o) (hdi : u.gpr .rdi = L.scr + BitVec.ofNat 64 st) (hdx : u.gpr .rdx = o)
    (hcx : u.gpr .rcx = L.scr + BitVec.ofNat 64 sWork) :
    WP isa (finF fFn) u fun u' => Ctx L g m₀ u' ∧ Frame [stR L st, workR L, ⟨o, 64⟩, ⟨L.B, 24⟩] u.mem u'.mem ∧
      ∀ m, P.T.S.Repr u.mem (L.scr + BitVec.ofNat 64 st) m → m.length < 2 ^ 64 →
        u.gpr .rsi = BitVec.ofNat 64 m.length → Spec.Sha256.bytesAt u'.mem o P.D = P.T.S.H.hash m := by
  refine WP.seq (WP.mono (ldFn_ok hL hc (o := fFn + 16) (by decide)) fun u₁ h₁ => ?_)
  obtain ⟨e, hW, hF, hew, hes⟩ := hFns h₁.ctx
  have h11 : u₁.gpr .r11 = L.ff := by rw [h₁.val, ← hc.pFf]; rfl
  have hm := hF.fin
  rw [← h11, hT] at hm
  have hz := P.sizes
  have hos : Region.Sub ⟨o, P.T.outBytes⟩ ⟨o, 64⟩ := Region.sub_prefix (by omega)
  refine VG.Proof.HashFns.X86_64.C.fin_icall P.T hF.consts hm hW (P.ok.choose_spec.2.local_)
    (h₁.ctx.fArgs hL hst ho ((h₁.keep .rdi (by decide)).trans hdi) ((h₁.keep .rdx (by decide)).trans hdx)
      ((h₁.keep .rcx (by decide)).trans hcx)) (h₁.ctx.fPass hew hes hst ho) fun u' A hW' hr => ?_
  obtain ⟨hc', hf⟩ := h₁.ctx.after hL (fin_safe ho hst) A hW hW'
  refine ⟨hc', h₁.mem ▸ hf.sub fun r hr => ?_, fun m hm hl hsi => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, sub_stR (by omega)⟩
    · exact ⟨_, by simp, hos⟩
    · exact ⟨_, by simp, sub_workR (by omega)⟩
    · exact ⟨_, by simp, sub_refl _⟩
  · rw [out_take]
    exact hr m (h₁.mem ▸ hm) hl ((h₁.keep .rsi (by decide)).trans hsi)

/-! ## The block `K ⊕ pad` -/

/-- The block `K ⊕ pad` of `B` bytes, for the key of `D` bytes at `K`
padded with zeros, with `c` in every byte of `pad`. -/
def padBlk (m : Mem) (K : Addr) (D B : Nat) (c : Byte) : List Byte :=
  (List.range B).map fun i => (if i < D then m (K + BitVec.ofNat 64 i) else 0) ^^^ c

theorem padBlk_length (m : Mem) (K : Addr) (D B : Nat) (c : Byte) : (padBlk m K D B c).length = B := by
  simp [padBlk]

/-- The block is HMAC's `K₀ ⊕ pad`, for a key no longer than a block. -/
theorem padBlk_eq (H : Spec.Hmac.HashFunction) (m : Mem) (K : Addr) {D : Nat} (hD : D ≤ H.blockSize) (c : Byte) :
    padBlk m K D H.blockSize c = Spec.Hmac.xorPad (Spec.Hmac.blockKey H (Spec.Sha256.bytesAt m K D)) c := by
  rw [Proof.Pbkdf2.MdKeys.blockKey_short H (by rw [Proof.Hmac.Common.bytesAt_length]; exact hD),
    Proof.Hmac.Common.bytesAt_length]
  apply List.ext_getElem (by simp [padBlk, Spec.Hmac.xorPad, Proof.Hmac.Common.bytesAt_length]; omega)
  intro i h₁ h₂
  simp only [padBlk, Spec.Hmac.xorPad, List.getElem_map, List.getElem_range]
  by_cases hi : i < D
  · simp only [hi, ↓reduceIte, List.getElem_append_left (show i < (Spec.Sha256.bytesAt m K D).length by
      rw [Proof.Hmac.Common.bytesAt_length]; exact hi)]
    simp [Spec.Sha256.bytesAt]
  · simp only [hi, ↓reduceIte]
    rw [List.getElem_append_right (by rw [Proof.Hmac.Common.bytesAt_length]; omega)]
    simp

/-- Word `j` of the block. -/
abbrev padW (m : Mem) (K : Addr) (D : Nat) (c : Byte) (j : Nat) : List Byte :=
  if 4 * (j + 1) ≤ D then (Spec.Sha256.bytesAt m (K + BitVec.ofNat 64 (4 * j)) 4).map (· ^^^ c)
  else List.replicate 4 c

theorem padW_length (m : Mem) (K : Addr) (D : Nat) (c : Byte) (j : Nat) : (padW m K D c j).length = 4 := by
  simp only [padW]; split <;> simp [Spec.Sha256.bytesAt]

theorem padBlk_take (m : Mem) (K : Addr) {D B j : Nat} (hD : D % 4 = 0) (hj : 4 * j + 4 ≤ B) (c : Byte) :
    (padBlk m K D B c).take (4 * j + 4) = (padBlk m K D B c).take (4 * j) ++ padW m K D c j := by
  apply List.ext_getElem (by simp [padBlk_length, padW_length]; omega)
  intro i h₁ h₂
  rw [List.getElem_take]
  by_cases hi : i < 4 * j
  · rw [List.getElem_append_left (by simp [padBlk_length]; omega), List.getElem_take]
  · have hl : ((padBlk m K D B c).take (4 * j)).length = 4 * j := by simp [padBlk_length]; omega
    have hi' : i - 4 * j < 4 := by simp [padBlk_length] at h₁; omega
    rw [List.getElem_append_right (by omega)]
    simp only [hl]
    simp only [padBlk, List.getElem_map, List.getElem_range, padW]
    by_cases hw : 4 * (j + 1) ≤ D
    · simp only [hw, ↓reduceIte, Spec.Sha256.bytesAt, List.getElem_map, List.getElem_range, show i < D by omega,
        Offset.add_add, show 4 * j + (i - 4 * j) = i by omega]
    · simp only [hw, ↓reduceIte, List.getElem_replicate, show ¬ i < D by omega]
      exact BitVec.zero_xor

/-- `ipad` and `opad` in each byte of a word. -/
theorem ipadW_eq : ipadW = Spec.Hmac.ipad ++ Spec.Hmac.ipad ++ Spec.Hmac.ipad ++ Spec.Hmac.ipad := by decide
theorem opadW_eq : opadW = Spec.Hmac.opad ++ Spec.Hmac.opad ++ Spec.Hmac.opad ++ Spec.Hmac.opad := by decide

theorem setWidth_32_64 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- Word `j` of `K ⊕ pad` (`c` in each byte of `pad`), with `scratch` in `rdi`. -/
theorem padWord_ok {u₀ u : State} (hc : Ctx L g m₀ u₀) (hrd : u.rd = u₀.rd) (hwr : u.wr = u₀.wr)
    (hsp : u.gpr .rsp = L.B + BitVec.ofNat 64 24) (hdi : u.gpr .rdi = L.scr) {D : Nat} (hD : D ≤ 64) {c : Byte}
    {j : Nat} (hj : 4 * j + 4 ≤ 128) :
    WP isa (.block (Cfg.padWord D (c ++ c ++ c ++ c) j)) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧
      u'.mem = writeBytes u.mem (L.scr + BitVec.ofNat 64 (sPad + 4 * j))
        (padW u.mem (L.B + BitVec.ofNat 64 24) D c j) := by
  have hst : InRegions u.wr (L.scr + BitVec.ofNat 64 (sPad + 4 * j)) 4 := by
    rw [hwr]; exact hc.inScrW (by simp only [sPad]; omega)
  unfold Cfg.padWord padW
  split
  · rename_i hk
    have hin : InRegions (u.rd ++ u.wr) (L.B + BitVec.ofNat 64 (24 + (fK + 4 * j))) 4 := by
      rw [hrd, hwr, hc.rd, hc.wr]
      exact ⟨L.FR, by simp, Offset.contains _ (by omega) (by simp only [fK]; have := L.he; omega)
        (by have := L.he; omega)⟩
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.load32, ea_stk, ea_at, hsp,
      Offset.add_add, hin, ite_true, Option.map_some, Option.bind_some, execAlu32, State.setReg32,
      RegUpd.gpr_setReg_self, RegUpd.gpr_arithFlags, setWidth_32_64, State.store32, RegUpd.gpr_setReg_of_ne _ _
        (show Reg.rdi ≠ .rax by decide), hdi, RegUpd.wr_setReg, RegUpd.wr_arithFlags, hst, Option.some.injEq,
      exists_eq_left']
    refine ⟨by triv, by triv, fun r hr => ?_, ?_⟩
    · simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]
    · simp only [RegUpd.mem_setReg, RegUpd.mem_arithFlags]
      rw [Proof.Pbkdf2.MdKeys.writeW_xorRep, show fK + 4 * j = 4 * j from Nat.zero_add _, ← Offset.add_add]
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, ea_at, Option.map_some,
      State.setReg32, RegUpd.gpr_setReg_self, setWidth_32_64, State.store32, RegUpd.gpr_setReg_of_ne _ _
        (show Reg.rdi ≠ .rax by decide), hdi, RegUpd.wr_setReg, hst, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨by triv, by triv, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, ?_⟩
    simp only [RegUpd.mem_setReg]
    rw [Proof.Pbkdf2.MdKeys.writeW_rep]

/-- The bytes of word `j` of the key, in memory changed only apart from the key. -/
theorem padW_frame {ws : List Region} {m m' : Mem} (hf : Frame ws m m') {K : Addr} {D : Nat} (hD : D ≤ 64)
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨K, 64⟩ r) (c : Byte) (j : Nat) : padW m' K D c j = padW m K D c j := by
  simp only [padW]
  split
  · rw [bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega))) (by omega)]
  · rfl

/-- The first `k` words of `K ⊕ pad`. -/
theorem padWords_ok (hL : L.Ok) {u₀ : State} (hc : Ctx L g m₀ u₀) {D B : Nat} (hD : D ≤ 64) (hD4 : D % 4 = 0)
    (hB : B ≤ 128) {c : Byte} :
    ∀ k, 4 * k ≤ B → ∀ u : State, u.rd = u₀.rd → u.wr = u₀.wr → u.gpr .rsp = L.B + BitVec.ofNat 64 24 →
      u.gpr .rdi = L.scr →
      WP isa (.block ((List.range k).flatMap (Cfg.padWord D (c ++ c ++ c ++ c)))) u fun u' =>
        u'.rd = u.rd ∧ u'.wr = u.wr ∧ (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧
        u'.mem = writeBytes u.mem (L.scr + BitVec.ofNat 64 sPad)
          ((padBlk u.mem (L.B + BitVec.ofNat 64 24) D B c).take (4 * k))
  | 0, _, u, _, _, _, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, fun _ _ => rfl, by
      simp only [Nat.mul_zero, List.take_zero, VG.WriteBytes.writeBytes_nil]⟩
  | k + 1, hk, u, hrd, hwr, hsp, hdi => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (padWords_ok hL hc hD hD4 hB k (by omega) u hrd hwr hsp hdi) fun u₁ ⟨h1, h2, h3, h4⟩ => ?_
    refine WP.mono (padWord_ok hc (h1.trans hrd) (h2.trans hwr) ((h3 .rsp (by decide)).trans hsp)
      ((h3 .rdi (by decide)).trans hdi) hD (j := k) (by omega)) fun u₂ ⟨g1, g2, g3, g4⟩ => ?_
    refine ⟨g1.trans h1, g2.trans h2, fun r hr => (g3 r hr).trans (h3 r hr), ?_⟩
    have hxl : ((padBlk u.mem (L.B + BitVec.ofNat 64 24) D B c).take (4 * k)).length = 4 * k := by
      simp [padBlk_length]; omega
    have hw : padW u₁.mem (L.B + BitVec.ofNat 64 24) D c k = padW u.mem (L.B + BitVec.ofNat 64 24) D c k := by
      rw [h4]
      refine padW_frame (writeBytes_frame _ _ _ (R := ⟨L.scr + BitVec.ofNat 64 sPad, 128⟩) ?_) hD
        (fun r hr => ?_) c k
      · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega
      · rw [List.mem_singleton] at hr; subst hr
        exact hL.stk_scr (by have := L.he; omega) (by simp only [sPad]; omega)
    rw [g4, hw, h4, show L.scr + BitVec.ofNat 64 (sPad + 4 * k) =
        L.scr + BitVec.ofNat 64 sPad + BitVec.ofNat 64 ((padBlk u.mem (L.B + BitVec.ofNat 64 24) D B c).take
          (4 * k)).length by rw [hxl, Offset.add_add],
      writeBytes_append _ _ _ _ (by rw [hxl, padW_length]; omega), ← padBlk_take _ _ hD4 (by omega),
      show 4 * (k + 1) = 4 * k + 4 by omega]

/-- `scratch` in `rdi`. -/
theorem scrPtr_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.scrPtr) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .rdi = L.scr := by
  have h208 := hc.inFr (d := 208) (by omega) (by have := L.he; omega)
  apply WP.of_runBlock
  simp only [Cfg.scrPtr, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk,
    hc.rsp, Offset.add_add, Nat.reduceAdd, h208, ite_true, Option.map_some, hc.pScr, RegUpd.gpr_setReg_self,
    RegUpd.mem_setReg, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL (d := .rdi) (by decide) rfl rfl rfl ⟨rfl, rfl⟩ fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, trivial,
    trivial⟩

/-- The block `K ⊕ pad` of `B` bytes, at `scratch + sPad`, with `scratch` in `rdi`. -/
theorem padBlock_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hdi : u.gpr .rdi = L.scr) {D B : Nat}
    (hD : D ≤ 64) (hD4 : D % 4 = 0) (hB : B ≤ 128) (hB4 : B % 4 = 0) {c : Byte} :
    WP isa (.block (Cfg.padBlock D B (c ++ c ++ c ++ c))) u fun u' => Ctx L g m₀ u' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 sPad, 128⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 sPad) B = padBlk u.mem (L.B + BitVec.ofNat 64 24) D B c := by
  rw [Cfg.padBlock]
  refine WP.mono_sf (padWords_ok hL hc hD hD4 hB (B / 4) (by omega) u rfl rfl hc.rsp hdi)
    fun u₂ ⟨h1, h2, h3, h4⟩ hsy => ?_
  have hR : (⟨L.scr + BitVec.ofNat 64 sPad, 128⟩ : Region).Contains (L.scr + BitVec.ofNat 64 sPad)
      ((padBlk u.mem (L.B + BitVec.ofNat 64 24) D B c).take (4 * (B / 4))).length := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, List.length_take, padBlk_length]
    omega
  have hf : Frame [⟨L.scr + BitVec.ofNat 64 sPad, 128⟩] u.mem u₂.mem := by
    rw [h4]; exact writeBytes_frame _ _ _ hR
  have hk : 4 * (B / 4) = B := by omega
  refine ⟨hc.keep hL h1 h2 (h3 .rsp (by decide))
      (fun r hr _ => h3 r (fun e => by subst e; exact absurd hr (by decide))) hf
      (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact safe_scr L (by simp only [sPad]; omega))
      hsy, hf, ?_⟩
  rw [h4, hk, List.take_of_length_le (by rw [padBlk_length])]
  have := Proof.Hmac.Common.bytesAt_writeBytes_self u.mem (L.scr + BitVec.ofNat 64 sPad)
    (padBlk u.mem (L.B + BitVec.ofNat 64 24) D B c) (by rw [padBlk_length]; omega)
  rwa [padBlk_length] at this

/-! ## HMAC -/

/-- A streaming state, in memory changed only apart from it. -/
theorem repr_frame {ws : List Region} {m m' : Mem} (hf : Frame ws m m') {p : Addr}
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨p, 192⟩ r) {msg : List Byte} (hr : P.T.S.Repr m p msg) :
    P.T.S.Repr m' p msg :=
  P.ok.choose_spec.2.local_ (fun i hi => Frame.bytes (R := ⟨p, 192⟩) hf hd (by simp only; omega)
    (by have := P.sizes.1; simp only; omega)) hr

/-- The key `K`: the first `D` bytes of the frame. -/
abbrev keyOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 24) P.D

theorem keyOf_frame {ws : List Region} {m m' : Mem} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 24, 64⟩ r) : keyOf P L m' = keyOf P L m :=
  bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by nums))) (by nums)

/-- The arguments of `update` of the state at `scratch + st`. -/
theorem updArgs_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {st cnt : Nat} (hst : st < 2 ^ 31)
    (hcnt : cnt < 2 ^ 32) {dataA : List Instr} {da : Addr}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .rdx da)) {len : Nat} (hlen : len < 2 ^ 32) :
    WP isa (.block (Cfg.updArgs st cnt dataA len)) u fun u' => Ctx L g m₀ u' ∧
      u'.mem = u.mem ∧ u'.gpr .rdi = L.scr + BitVec.ofNat 64 st ∧ u'.gpr .rsi = BitVec.ofNat 64 cnt ∧
      u'.gpr .rdx = da ∧ u'.gpr .rcx = BitVec.ofNat 64 len ∧ u'.gpr .r8 = L.scr + BitVec.ofNat 64 sWork := by
  rw [Cfg.updArgs, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .rdi) (by decide) hst) fun u₁ h₁ => ?_
  refine WP.mono (mov32_ok hL h₁.ctx (d := .rsi) (by decide) hcnt) fun u₂ h₂ => ?_
  refine WP.mono (hdA u₂ h₂.ctx) fun u₃ h₃ => ?_
  refine WP.mono (mov32_ok hL h₃.ctx (d := .rcx) (by decide) hlen) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .r8) (by decide) (a := sWork) (by decide)) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₅.keep _ (by decide), h₄.val]

/-- The arguments of `finalize` of the state at `scratch + st`. -/
theorem finArgs_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {st cnt : Nat} (hst : st < 2 ^ 31)
    (hcnt : cnt < 2 ^ 32) {outA : List Instr} {o : Addr}
    (hoA : ∀ u, Ctx L g m₀ u → WP isa (.block outA) u (Upd L g m₀ u .rdx o)) :
    WP isa (.block (Cfg.finArgs st cnt outA)) u fun u' => Ctx L g m₀ u' ∧
      u'.mem = u.mem ∧ u'.gpr .rdi = L.scr + BitVec.ofNat 64 st ∧ u'.gpr .rsi = BitVec.ofNat 64 cnt ∧
      u'.gpr .rdx = o ∧ u'.gpr .rcx = L.scr + BitVec.ofNat 64 sWork := by
  rw [Cfg.finArgs, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .rdi) (by decide) hst) fun u₁ h₁ => ?_
  refine WP.mono (mov32_ok hL h₁.ctx (d := .rsi) (by decide) hcnt) fun u₂ h₂ => ?_
  refine WP.mono (hoA u₂ h₂.ctx) fun u₃ h₃ => ?_
  refine WP.mono (scr_ok hL h₃.ctx (d := .rcx) (by decide) (a := sWork) (by decide)) fun u₄ h₄ => ?_
  refine ⟨h₄.ctx, by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, h₄.val⟩
  · rw [h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₄.keep _ (by decide), h₃.val]

theorem frame_cons_sub {ws ws' : List Region} {m m' : Mem} (hf : Frame ws m m')
    (h : ∀ r ∈ ws, r ∈ ws') : Frame ws' m m' :=
  hf.sub fun r hr => ⟨r, h r hr, sub_refl _⟩

/-- The state at `scratch + st` set to `init`, then `update` with `K ⊕ pad`. -/
theorem keyed_ok (hL : L.Ok) (hT : L.T = P.T) {u : State} (hc : Ctx L g m₀ u) {st : Nat} (hst : st + 192 ≤ 384)
    {pad : BitVec 32} {c : Byte} (hp : pad = c ++ c ++ c ++ c) :
    WP isa ((cfgOf P).keyed st pad) u fun u' => Ctx L g m₀ u' ∧
      Frame [stR L st, workR L, ⟨L.B, 24⟩] u.mem u'.mem ∧
      P.T.S.Repr u'.mem (L.scr + BitVec.ofNat 64 st)
        (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.T.S.H (keyOf P L u.mem)) c) := by
  have hz := P.sizes
  have hsw : sWork = 384 := rfl
  have hsp : sPad = 1792 := rfl
  have hK : ∀ r ∈ [stR L st, workR L, ⟨L.B, 24⟩], Region.Disjoint ⟨L.B + BitVec.ofNat 64 24, 64⟩ r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hL.stk_scr (by have := L.he; omega) (by omega)
    · exact hL.stk_scr (by have := L.he; omega) (by omega)
    · exact Offset.disjoint_base _ (by omega) (by have := hL.nb; have := L.he; omega)
  rw [Cfg.keyed, cfgOf_D, cfgOf_B, hp]
  refine WP.seq (WP.mono (scr_ok hL hc (d := .rdi) (by decide) (a := st) (by omega)) fun u₁ h₁ => ?_)
  refine WP.seq (WP.mono (init_ok hL hT h₁.ctx hst h₁.val) fun u₂' ⟨hc₂', hf₂, hr₂'⟩ => ?_)
  refine WP.seq (WP.mono (scrPtr_ok hL hc₂') fun u₂ ⟨hc₂, hm₂, hdi₂⟩ => ?_)
  rw [← hm₂] at hf₂ hr₂'
  have hr₂ := hr₂'
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (padBlock_ok hL hc₂ hdi₂ (D := P.D) (B := P.B) (c := c) (by omega) (by omega) (by omega)
    (by omega)) fun u₃ ⟨hc₃, hf₃, hb₃⟩ => ?_
  refine WP.mono (updArgs_ok hL hc₃ (st := st) (cnt := 0) (by omega) (by decide)
    (fun u hcu => scr_ok hL hcu (d := .rdx) (by decide) (a := sPad) (by decide)) (len := P.B) (by omega))
    fun u₄ ⟨hc₄, hm₄, hdi, hsi, hdx, hcx, h8⟩ => ?_
  refine WP.mono (upd_ok hL hT hc₄ hst (.inr ⟨sPad, rfl, by decide, by omega⟩) hdi hdx hcx (by omega) h8)
    fun u₅ ⟨hc₅, hf₅, hr₅⟩ => ⟨hc₅, ?_, ?_⟩
  · refine (frame_cons_sub (h₁.mem ▸ hf₂) (by simp)).trans ((hf₃.sub fun r hr => ⟨workR L, by simp, ?_⟩).trans
      (hm₄ ▸ hf₅))
    rw [List.mem_singleton] at hr; subst hr
    exact Offset.sub _ (by omega) (by omega)
  · have hr₄ : P.T.S.Repr u₄.mem (L.scr + BitVec.ofNat 64 st) [] := by
      rw [hm₄]
      refine repr_frame hf₃ (fun r hr => ?_) hr₂
      rw [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    have := hr₅ [] hr₄ (by rw [hsi]; rfl)
    have hBB : P.B = P.T.S.H.blockSize := rfl
    rwa [List.nil_append, hm₄, hb₃, hBB, padBlk_eq P.T.S.H _ _ (by omega), show Spec.Sha256.bytesAt u₂.mem
      (L.B + BitVec.ofNat 64 24) P.D = keyOf P L u.mem from
        (keyOf_frame hf₂ fun r hr => hK r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
          rcases hr with h | h <;> simp [h])).trans (by rw [h₁.mem])] at this

theorem mem_sub {α : Type} {l l' : List α} (h : l ⊆ l') {r : α} (hr : r ∈ l) : r ∈ l' := h hr

theorem keyOf_length (m : Mem) : (keyOf P L m).length = P.D := Proof.Hmac.Common.bytesAt_length _ _ _

/-- The key padded to a block. -/
theorem blockKey_length (m : Mem) : (Spec.Hmac.blockKey P.T.S.H (keyOf P L m)).length = P.B := by
  have hz := P.sizes
  have hBB : P.B = P.T.S.H.blockSize := rfl
  rw [Proof.Pbkdf2.MdKeys.blockKey_short _ (by rw [keyOf_length, ← hBB]; omega), List.length_append,
    List.length_replicate, keyOf_length, ← hBB]
  omega

theorem hash_length (m : List Byte) : (P.T.S.H.hash m).length = P.D := by
  obtain ⟨H, -, hok⟩ := P.ok
  rw [← hok.hash, hok.valid.2 m, hok.len]

theorem xorPad_length (k : List Byte) (c : Byte) : (Spec.Hmac.xorPad k c).length = k.length := List.length_map _

/-- After `HMAC_K(data)`: the MAC in the frame at `dst`. -/
structure Done (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 64) (m₀ : Mem) (t : State) (da : Addr)
    (len dst : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 2256⟩, ⟨L.B, 24⟩, ⟨L.B + BitVec.ofNat 64 (24 + dst), 64⟩] t.mem u.mem
  mac : Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (24 + dst)) P.D =
    P.mac (keyOf P L t.mem) (Spec.Sha256.bytesAt t.mem da len)

/-- `HMAC_K(data)`, for the key `K` in the frame, to the frame at `dst`. -/
theorem hmac_ok (hL : L.Ok) (hT : L.T = P.T) {t : State} (hc : Ctx L g m₀ t) {dataA : List Instr} {da : Addr}
    {len dst : Nat} (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .rdx da))
    (hd : DataOk L da len) (hlen : len ≤ 256) (hdst : dst + 64 ≤ 128) :
    WP isa ((cfgOf P).hmac dataA len dst) t (Done P L g m₀ t da len dst) := by
  have hz := P.sizes
  have hsw : sWork = 384 := rfl
  have hst : sTmp = 1920 := rfl
  have hsi : sInner = 0 := rfl
  have hso : sOuter = 192 := rfl
  have hle := L.he
  have hnb := hL.nb
  -- Where the calls write, within what HMAC changes.
  have hsub : ∀ r ∈ [stR L sInner, stR L sOuter, workR L, ⟨L.scr + BitVec.ofNat 64 sTmp, 64⟩, ⟨L.B, 24⟩,
      ⟨L.B + BitVec.ofNat 64 (24 + dst), 64⟩], ∃ r' ∈ [(⟨L.scr, 2256⟩ : Region), ⟨L.B, 24⟩,
        ⟨L.B + BitVec.ofNat 64 (24 + dst), 64⟩], Region.Sub r r' := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨⟨L.scr, 2256⟩, by simp, Offset.sub_base _ (by omega)⟩
    · exact ⟨⟨L.scr, 2256⟩, by simp, Offset.sub_base _ (by omega)⟩
    · exact ⟨⟨L.scr, 2256⟩, by simp, Offset.sub_base _ (by omega)⟩
    · exact ⟨⟨L.scr, 2256⟩, by simp, Offset.sub_base _ (by omega)⟩
    · exact ⟨⟨L.B, 24⟩, by simp, sub_refl _⟩
    · exact ⟨⟨L.B + BitVec.ofNat 64 (24 + dst), 64⟩, by simp, sub_refl _⟩
  have widen : ∀ {ws : List Region} {m m' : Mem}, Frame ws m m' →
      (∀ r ∈ ws, r ∈ [stR L sInner, stR L sOuter, workR L, ⟨L.scr + BitVec.ofNat 64 sTmp, 64⟩, ⟨L.B, 24⟩,
        ⟨L.B + BitVec.ofNat 64 (24 + dst), 64⟩]) →
      Frame [⟨L.scr, 2256⟩, ⟨L.B, 24⟩, ⟨L.B + BitVec.ofNat 64 (24 + dst), 64⟩] m m' :=
    fun hf hw => hf.sub fun r hr => hsub r (hw r hr)
  -- The states are apart from what the other calls write.
  have hIn : ∀ r ∈ [stR L sOuter, workR L, ⟨L.scr + BitVec.ofNat 64 sTmp, 64⟩, ⟨L.B, 24⟩],
      Region.Disjoint ⟨L.scr + BitVec.ofNat 64 sInner, 192⟩ r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact (hL.low_scr (by omega)).symm
  have hOut : ∀ r ∈ [stR L sInner, workR L, ⟨L.scr + BitVec.ofNat 64 sTmp, 64⟩, ⟨L.B, 24⟩],
      Region.Disjoint ⟨L.scr + BitVec.ofNat 64 sOuter, 192⟩ r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact (hL.low_scr (by omega)).symm
  -- The key and the data are apart from what the calls before them write.
  have hKey : ∀ r ∈ [stR L sInner, stR L sOuter, workR L, ⟨L.B, 24⟩],
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 24, 64⟩ r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hL.stk_scr (by omega) (by omega)
    · exact hL.stk_scr (by omega) (by omega)
    · exact hL.stk_scr (by omega) (by omega)
    · exact Offset.disjoint_base _ (by omega) (by omega)
  have hData : ∀ r ∈ [stR L sInner, stR L sOuter, workR L, ⟨L.B, 24⟩], Region.Disjoint ⟨da, len⟩ r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hd.work hL (by omega)
    · exact hd.work hL (by omega)
    · exact hd.work hL (by omega)
    · exact hd.low hL
  have hTmp : ∀ r ∈ [stR L sOuter, workR L, ⟨L.B, 24⟩],
      Region.Disjoint ⟨L.scr + BitVec.ofNat 64 sTmp, P.D⟩ r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact (hL.low_scr (by omega)).symm
  have hDl : (Spec.Sha256.bytesAt t.mem da len).length = len := Proof.Hmac.Common.bytesAt_length _ _ _
  rw [Cfg.hmac, cfgOf_B, cfgOf_D]
  -- The keyed states.
  refine WP.seq (WP.mono (keyed_ok hL hT hc (st := sInner) (by omega) ipadW_eq) fun u₁ ⟨hc₁, hf₁, hr₁⟩ => ?_)
  refine WP.seq (WP.mono (keyed_ok hL hT hc₁ (st := sOuter) (by omega) opadW_eq) fun u₂ ⟨hc₂, hf₂, hr₂⟩ => ?_)
  have hk₁ : keyOf P L u₁.mem = keyOf P L t.mem :=
    keyOf_frame hf₁ fun r hr => hKey r (mem_sub (by simp) hr)
  rw [hk₁] at hr₂
  have hr₁' := repr_frame hf₂ (fun r hr => hIn r (mem_sub (by simp) hr)) hr₁
  have hdata₂ : Spec.Sha256.bytesAt u₂.mem da len = Spec.Sha256.bytesAt t.mem da len := by
    rw [bytesAt_frame hf₂ (fun r hr => hData r (mem_sub (by simp) hr)) (by omega),
      bytesAt_frame hf₁ (fun r hr => hData r (mem_sub (by simp) hr)) (by omega)]
  -- The inner `update` with the data.
  refine WP.seq (WP.mono (updArgs_ok hL hc₂ (st := sInner) (cnt := P.B) (by decide) (by omega) hdA
    (len := len) (by omega)) fun u₃ ⟨hc₃, hm₃, hdi₃, hsi₃, hdx₃, hcx₃, h8₃⟩ => ?_)
  refine WP.seq (WP.mono (upd_ok hL hT hc₃ (st := sInner) (by omega) hd.upd hdi₃ hdx₃ hcx₃ (by omega) h8₃)
    fun u₄ ⟨hc₄, hf₄, hr₄⟩ => ?_)
  have hr₄' := hr₄ _ (hm₃ ▸ hr₁') (by rw [hsi₃, xorPad_length, blockKey_length])
  rw [hm₃, hdata₂] at hr₄'
  have hr₂' := repr_frame hf₄ (fun r hr => hOut r (mem_sub (by simp) hr)) (hm₃ ▸ hr₂)
  -- The inner `finalize`, to the inner hash.
  refine WP.seq (WP.mono (finArgs_ok hL hc₄ (st := sInner) (cnt := P.B + len) (by decide) (by omega)
    (fun u hcu => scr_ok hL hcu (d := .rdx) (by decide) (a := sTmp) (by decide)))
    fun u₅ ⟨hc₅, hm₅, hdi₅, hsi₅, hdx₅, hcx₅⟩ => ?_)
  refine WP.seq (WP.mono (fin_ok hL hT hc₅ (st := sInner) (by omega) (.inr rfl) hdi₅ hdx₅ hcx₅)
    fun u₆ ⟨hc₆, hf₆, hr₆⟩ => ?_)
  have hih := hr₆ _ (hm₅ ▸ hr₄') (by simp only [List.length_append, xorPad_length, blockKey_length, hDl]; omega)
    (by simp only [hsi₅, List.length_append, xorPad_length, blockKey_length, hDl])
  have hr₂'' := repr_frame hf₆ (fun r hr => hOut r (mem_sub (by simp) hr)) (hm₅ ▸ hr₂')
  -- The outer `update` with the inner hash.
  refine WP.seq (WP.mono (updArgs_ok hL hc₆ (st := sOuter) (cnt := P.B) (by decide) (by omega)
    (fun u hcu => scr_ok hL hcu (d := .rdx) (by decide) (a := sTmp) (by decide)) (len := P.D) (by omega))
    fun u₇ ⟨hc₇, hm₇, hdi₇, hsi₇, hdx₇, hcx₇, h8₇⟩ => ?_)
  refine WP.seq (WP.mono (upd_ok hL hT hc₇ (st := sOuter) (by omega) (.inr ⟨sTmp, rfl, by omega, by omega⟩)
    hdi₇ hdx₇ hcx₇ (by omega) h8₇) fun u₈ ⟨hc₈, hf₈, hr₈⟩ => ?_)
  have hr₈' := hr₈ _ (hm₇ ▸ hr₂'') (by rw [hsi₇, xorPad_length, blockKey_length])
  rw [hm₇, hih] at hr₈'
  -- The outer `finalize`, to `dst`.
  refine WP.seq (WP.mono (finArgs_ok hL hc₈ (st := sOuter) (cnt := P.B + P.D) (by decide) (by omega)
    (fun u hcu => fr_ok hL hcu (d := .rdx) (by decide) (o := dst) (by omega)))
    fun u₉ ⟨hc₉, hm₉, hdi₉, hsi₉, hdx₉, hcx₉⟩ => ?_)
  refine WP.mono (fin_ok hL hT hc₉ (st := sOuter) (by omega) (.inl ⟨dst, rfl, hdst⟩) hdi₉ hdx₉ hcx₉)
    fun u₁₀ ⟨hc₁₀, hf₁₀, hr₁₀⟩ => ⟨hc₁₀, ?_, ?_⟩
  · refine (widen hf₁ (fun _ hr => mem_sub (by simp) hr)).trans ((widen hf₂ (fun _ hr => mem_sub (by simp) hr)).trans
      ?_)
    rw [← hm₃]
    refine (widen hf₄ (fun _ hr => mem_sub (by simp) hr)).trans ?_
    rw [← hm₅]
    refine (widen hf₆ (fun _ hr => mem_sub (by simp) hr)).trans ?_
    rw [← hm₇]
    refine (widen hf₈ (fun _ hr => mem_sub (by simp) hr)).trans ?_
    rw [← hm₉]
    exact widen hf₁₀ (fun _ hr => mem_sub (by simp) hr)
  · rw [hr₁₀ _ (hm₉ ▸ hr₈') (by simp only [List.length_append, xorPad_length, blockKey_length, hash_length]; omega)
      (by simp only [hsi₉, List.length_append, xorPad_length, blockKey_length, hash_length])]
    rfl

end VG.Proof.Ecdsa.Rfc6979.X86_64
