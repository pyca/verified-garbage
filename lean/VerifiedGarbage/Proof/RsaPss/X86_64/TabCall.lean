module

public import VerifiedGarbage.Proof.RsaPss.X86_64.Basic
public import VerifiedGarbage.Proof.Framework.ICall
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Impl.RsaPss.X86_64
public import VerifiedGarbage.Impl.MdHashTable.X86_64
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-!
# RSASSA-PSS on x86-64: the calls through the tables' slots

`scall s ts` (`Impl/RsaPss/X86_64.lean`) runs as the call of the function
of `ts` whose address the slot `s` holds (`scall_ok`), when that function is
the first of `ts` at that address (as `TabOK` says of the tables of a
registration whose functions of distinct names are at distinct addresses).
`HT`: the slots of the table of `MdHash` hold the addresses of a hash
function's `init`, compression function and digest (`dn`), which the calls
of `MdFns` reach, in a view `W` of the frame's words; it holds of any view
that differs from `W` only in other words (`HT.upd`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Proof.Bignum (off word)

/-- The call of the function whose address the slot `s` (frame word `k`)
holds, `n`'s. -/
theorem scall_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {s k : Nat} (hk : s = 8 * k) (hkn : k < nW) (hs8 : s + 8 ≤ frameBytes) {n : String}
    {c : Prog isa} {ts : List (String × Prog isa)} (hw : W k = t.syms n)
    (hf : ts.find? (fun q => t.syms q.1 == t.syms n) = some (n, c)) {Q : State → Prop}
    (h : ∀ t', Keep [.r11] t t' → t'.mem = t.mem → t'.syms = t.syms → WP isa (.call n c) t' Q) :
    WP isa (scall s ts) t Q := by
  refine WP.seq (WP.mono (WP.keep [.r11] (Q := fun t' => t'.gpr .r11 = t.syms n ∧ t'.mem = t.mem ∧
      t'.syms = t.syms) ?_ rfl) fun t' ⟨⟨h11, hm, hsy⟩, k⟩ => ?_)
  · xrun [ea_sp, L.rsp, L.ld (d := s) hs8, R.rd k hk hkn, hw, setReg_syms]
  · refine WP.icalls_of_call (a := t.syms n) (by simp only [icall, h11]) ?_ (h t' k hm hsy)
    show ts.find? (fun q => t'.syms q.1 == t.syms n) = _
    rw [hsy]; exact hf

theorem upd_ne' {α : Type} {f : Nat → α} {a x : Nat} (h : x ≠ a) (v : α) : upd f a v x = f x := by
  simp [upd, h]

/-- The slots of the table of `MdHash` (frame words 8, 9 and 10) hold the
addresses `sy` gives `H`'s `init`, compression function and digest (`dn`,
whose code is `digest H.P`), which the calls of `f` reach. -/
structure HT (H : Impl.Pbkdf2.Md.X86_64.Hash) (dn : String) (f : MdFns) (W : Nat → BitVec 64)
    (sy : String → Addr) : Prop where
  wi : W 8 = sy H.initN
  wc : W 9 = sy H.compN
  wd : W 10 = sy dn
  fi : f.init.find? (fun q => sy q.1 == sy H.initN) = some (H.initN, H.initC)
  fc : f.comp.find? (fun q => sy q.1 == sy H.compN) = some (H.compN, H.compC)
  fd : f.dig.find? (fun q => sy q.1 == sy dn) = some (dn, Impl.MdHashTable.X86_64.digest H.P)

theorem HT.upd {H : Impl.Pbkdf2.Md.X86_64.Hash} {dn : String} {f : MdFns} {W : Nat → BitVec 64}
    {sy : String → Addr} (h : HT H dn f W sy) {k : Nat} (hk : k ≠ 8 ∧ k ≠ 9 ∧ k ≠ 10) (v : BitVec 64) :
    HT H dn f (upd W k v) sy :=
  ⟨(upd_ne' (Ne.symm hk.1) v).trans h.wi, (upd_ne' (Ne.symm hk.2.1) v).trans h.wc,
    (upd_ne' (Ne.symm hk.2.2) v).trans h.wd, h.fi, h.fc, h.fd⟩

theorem HT.congr {H : Impl.Pbkdf2.Md.X86_64.Hash} {dn : String} {f : MdFns} {W W' : Nat → BitVec 64}
    {sy sy' : String → Addr} (h : HT H dn f W sy) (hsy : sy' = sy) (h8 : W' 8 = W 8) (h9 : W' 9 = W 9)
    (h10 : W' 10 = W 10) : HT H dn f W' sy' := by
  subst hsy
  exact ⟨h8.trans h.wi, h9.trans h.wc, h10.trans h.wd, h.fi, h.fc, h.fd⟩

/-- What the calls of the digest of `H` need of its code, which the kernel
checks of each hash function: it never loads MXCSR or writes `rsp`, and
writes only `r8`, `r9`, `rbx`, `rbp` (which it restores) and `rax`. -/
structure DigOK (H : Impl.Pbkdf2.Md.X86_64.Hash) : Prop where
  mx : (Impl.MdHashTable.X86_64.digest H.P).allInstrs (fun i => !loadsMxcsr i) = true
  sp : NoSp (Impl.MdHashTable.X86_64.digest H.P)
  cl : ∀ r, r ∉ [Reg.r8, .r9, .rbx, .rbp, .rax] →
    ∀ i ∈ instrs (Impl.MdHashTable.X86_64.digest H.P), Taint.clobbers i r = false

end VG.Proof.RsaPss.X86_64
