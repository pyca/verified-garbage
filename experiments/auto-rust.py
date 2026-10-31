from pathlib import Path
import sys
script=Path(__file__).resolve().parent
root=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else script
checkout=Path(sys.argv[2]).resolve() if len(sys.argv)>2 else root.parent/'mldsa-measure'
s='// UNPROVED automatic prepared-key experiment; AArch64 only. Do not ship.\n'+(root/'original-mldsa_common.rs').read_text()
s=s.replace('macro_rules! ml_dsa {',(script/'auto-cache-helper.rs').read_text()+'\nmacro_rules! ml_dsa {')
s=s.replace('    pk: $pk:literal,','    k: $k:literal,\n    l: $l:literal,\n    eta: $eta:literal,\n    pk: $pk:literal,')
needle='        keygen: $keygen:path,'
s=s.replace(needle,'''        sign_prepared: $sign_prepared:path,
        verify_prepared: $verify_prepared:path,
        sign_message_prepared: $sign_message_prepared:path,
        verify_message_prepared: $verify_message_prepared:path,
        sign_prepared_sha3: $sign_prepared_sha3:path,
        verify_prepared_sha3: $verify_prepared_sha3:path,
        sign_message_prepared_sha3: $sign_message_prepared_sha3:path,
        verify_message_prepared_sha3: $verify_message_prepared_sha3:path,
'''+needle)
cfg='#[cfg(all(target_arch = "aarch64", feature = "alloc"))]'
vtype='$crate::mldsa_common::auto_cache::Cache<$crate::mldsa_common::auto_cache::Prepared<{ $pk + 1024 * $k }, false>>'
stype='$crate::mldsa_common::auto_cache::Cache<$crate::mldsa_common::auto_cache::Prepared<{ $sk + 1024 * ($l + 2 * $k) }, true>>'
s=s.replace('            bytes: [u8; $pk],',f'            bytes: [u8; $pk],\n            {cfg}\n            cache: {vtype},')
s=s.replace('            sk: [u8; $sk],',f'            sk: [u8; $sk],\n            {cfg}\n            cache: {stype},')
s=s.replace('                    bytes: *bytes,',f'                    bytes: *bytes,\n                    {cfg}\n                    cache: $crate::mldsa_common::auto_cache::Cache::new(),')
s=s.replace('                        bytes: [0; $pk],',f'                        bytes: [0; $pk],\n                        {cfg}\n                        cache: $crate::mldsa_common::auto_cache::Cache::new(),')
s=s.replace('                    sk: [0; $sk],',f'                    sk: [0; $sk],\n                    {cfg}\n                    cache: $crate::mldsa_common::auto_cache::Cache::new(),')
public_prep='''
            #[cfg(all(target_arch = "aarch64", feature = "alloc"))]
            fn prepared(&self) -> Option<&$crate::mldsa_common::auto_cache::Prepared<{ $pk + 1024 * $k }, false>> {
                self.cache.get(|| {
                    let mut prepared = $crate::mldsa_common::auto_cache::Prepared::allocate()?;
                    prepared.bytes[..$pk].copy_from_slice(&self.bytes);
                    let mut work = core::mem::MaybeUninit::<[u64; 128]>::uninit();
                    for i in 0..$k {
                        // UNPROVED: composing existing unpack/NTT, new layout not yet proved.
                        unsafe {
                            let input = prepared.bytes.as_ptr().add(32 + 320 * i).cast();
                            let output = prepared.bytes.as_mut_ptr().add($pk + 1024 * i).cast();
                            $crate::arch::mldsa::vg_mldsa_unpack_t1(input, output);
                            $crate::arch::mldsa::vg_mldsa_ntt(output, work.as_mut_ptr());
                        }
                    }
                    unsafe { $crate::zeroize::zeroize_raw(work.as_mut_ptr().cast(), 1024); }
                    Some(prepared)
                })
            }
'''
secret_prep='''
            #[cfg(all(target_arch = "aarch64", feature = "alloc"))]
            fn prepared(&self) -> Option<&$crate::mldsa_common::auto_cache::Prepared<{ $sk + 1024 * ($l + 2 * $k) }, true>> {
                self.cache.get(|| {
                    let mut prepared = $crate::mldsa_common::auto_cache::Prepared::allocate()?;
                    prepared.bytes[..$sk].copy_from_slice(&self.sk);
                    let mut work = core::mem::MaybeUninit::<[u64; 128]>::uninit();
                    let slen = if $eta == 2 { 96 } else { 128 };
                    for i in 0..($l + 2 * $k) {
                        let (offset, len, a, b) = if i < $l + $k {
                            (128 + slen * i, slen, $eta, $eta)
                        } else {
                            (128 + slen * ($l + $k) + 416 * (i - $l - $k), 416, 4095, 4096)
                        };
                        // UNPROVED: composing existing unpack/NTT, new layout not yet proved.
                        unsafe {
                            let input = prepared.bytes.as_ptr().add(offset);
                            let output = prepared.bytes.as_mut_ptr().add($sk + 1024 * i).cast();
                            $crate::arch::mldsa::vg_mldsa_bit_unpack(input, len, a, b, output);
                            $crate::arch::mldsa::vg_mldsa_ntt(output, work.as_mut_ptr());
                        }
                    }
                    unsafe { $crate::zeroize::zeroize_raw(work.as_mut_ptr().cast(), 1024); }
                    Some(prepared)
                })
            }
'''
s=s.replace('        impl $VerifyingKey {','        impl $VerifyingKey {\n'+public_prep)
s=s.replace('        impl $SigningKey {','        impl $SigningKey {\n'+secret_prep)
# Preserve ordinary dispatch and expose separate prepared entries generated by Lean.
for method,call in [
 ('pub fn verify(', '$verify_message_prepared'),
 ('pub fn verify_mu(', '$verify_prepared'),
 ('fn sign_with(', '$sign_message_prepared'),
 ('pub fn sign_mu(', '$sign_prepared')]:
 pos=s.index(method)
 start=s.index('let r = unsafe {',pos)
 opening=s.index('{',start); depth=1; end=opening+1
 while depth:
  if s[end]=='{': depth+=1
  elif s[end]=='}': depth-=1
  end+=1
 old=s[opening+1:end-1]
 if method=='pub fn verify(':
  args='key, m, m_len, c, c_len, sig, scratch.as_mut_ptr(), &self.tr'
 elif method=='pub fn verify_mu(':
  args='key, mu, sig, scratch.as_mut_ptr()'
 elif method=='fn sign_with(':
  args='key, m, m_len, c, c_len, rnd, &mut sig, scratch.as_mut_ptr()'
 else:
  args='key, mu, rnd, &mut sig, scratch.as_mut_ptr()'
 prepared=f'''let key = prepared.bytes.as_ptr().cast();
                            match backend() {{
                                Backend::Scalar => {call}({args}),
                                Backend::Sha3 => {call}_sha3({args}),
                            }}'''
 replacement='''let r = unsafe {
                    #[cfg(all(target_arch = "aarch64", feature = "alloc"))]
                    { if let Some(prepared) = self.prepared() {
                            '''+prepared+'''
                        } else {'''+old+''' } }
                    #[cfg(not(all(target_arch = "aarch64", feature = "alloc")))]
                    {'''+old+''' }
                }'''
 s=s[:start]+replacement+s[end:]
 # Reject invalid public context lengths before they can trigger preparation.
 if method in ('pub fn verify(', 'fn sign_with('):
  pos=s.index(method); opening=s.index('{',pos)
  s=s[:opening+1]+'''\n                if ctx.len() > 255 { return Err(Error::ContextTooLong); }'''+s[opening+1:]
(checkout/'src/mldsa_common.rs').write_text(s)
for n,k,l,eta in [(44,4,4,2),(65,6,5,4),(87,8,7,2)]:
 s=(root/f'original-mldsa{n}.rs').read_text()
 s=s.replace('    pk: ',f'    k: {k},\n    l: {l},\n    eta: {eta},\n    pk: ')
 extra=''
 for suffix in ('','_sha3'):
  for field,op in [('sign','sign'),('verify','verify'),('sign_message','sign_message'),('verify_message','verify_message_cached')]:
   extra+=f'    {field}_prepared{suffix}: crate::arch::mldsa{n}::vg_mldsa{n}_{op}{suffix}_prepared,\n'
 s=s.replace('    keygen: ',extra+'    keygen: ')
 (checkout/f'src/mldsa{n}.rs').write_text(s)
