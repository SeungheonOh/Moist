import Lake
open Lake DSL

package moist where
  version := v!"0.1.0"

-- Build the Zig FFI static library (plutuz CEK machine)
extern_lib libplutuz_ffi (pkg : NPackage _) := do
  let ffiName := nameToStaticLib "plutuz_ffi"
  let blstName := nameToStaticLib "blst"
  proc {
    cmd := "env"
    args := #["-u", "DYLD_LIBRARY_PATH", "-u", "LD_LIBRARY_PATH", "zig", "build"]
    cwd := pkg.dir / "ffi"
  }
  let zigOut := pkg.dir / "ffi" / "zig-out" / "lib"
  IO.FS.createDirAll pkg.staticLibDir
  IO.FS.writeBinFile (pkg.staticLibDir / ffiName) (← IO.FS.readBinFile (zigOut / ffiName))
  IO.FS.writeBinFile (pkg.staticLibDir / blstName) (← IO.FS.readBinFile (zigOut / blstName))
  return pure (pkg.staticLibDir / ffiName)

-- blst dependency (symbols referenced by plutuz_ffi)
extern_lib libblst (pkg : NPackage _) := do
  return pure (pkg.staticLibDir / nameToStaticLib "blst")

-- C shim wrapping lean.h inline functions for Zig FFI
extern_lib liblean_shim (pkg : NPackage _) := do
  let leanIncDir := (← getLeanSysroot) / "include"
  let name := nameToStaticLib "lean_shim"
  let oFile := pkg.buildDir / "ffi" / "lean_shim.o"
  IO.FS.createDirAll (pkg.buildDir / "ffi")
  proc {
    cmd := "cc"
    args := #["-c", "-O2", "-I", leanIncDir.toString,
              "-o", oFile.toString,
              (pkg.dir / "ffi" / "lean_shim.c").toString]
  }
  proc {
    cmd := "ar"
    args := #["rcs", (pkg.staticLibDir / name).toString, oFile.toString]
  }
  return pure (pkg.staticLibDir / name)

@[default_target]
lean_lib Moist where
  precompileModules := true

lean_lib Test

lean_exe moist where
  root := `Main

@[test_driver]
lean_exe tests where
  root := `TestMain

lean_exe nft_test where
  root := `Test.Onchain.Testing
