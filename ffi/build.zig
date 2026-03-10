const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});

    // Get blst dependency (same version as plutuz uses)
    const blst_dep = b.dependency("blst", .{});

    // Build blst C code
    const blst_module = b.createModule(.{
        .target = target,
        .optimize = .ReleaseFast,
        .link_libc = true,
    });
    blst_module.addIncludePath(blst_dep.path("bindings"));
    blst_module.addIncludePath(blst_dep.path("src"));
    blst_module.addCSourceFile(.{
        .file = blst_dep.path("src/server.c"),
        .flags = &.{ "-fno-builtin", "-Wno-unused-function" },
    });

    const cpu_arch = target.result.cpu.arch;
    if (cpu_arch == .x86_64 or cpu_arch == .aarch64) {
        blst_module.addCMacro("__BLST_PORTABLE__", "1");
        blst_module.addAssemblyFile(blst_dep.path("build/assembly.S"));
    } else {
        blst_module.addCMacro("__BLST_PORTABLE__", "1");
    }

    const blst_lib = b.addLibrary(.{
        .linkage = .static,
        .name = "blst",
        .root_module = blst_module,
    });

    // Get plutuz dependency and create its module
    const plutuz_dep = b.dependency("plutuz", .{});

    const plutuz_mod = b.createModule(.{
        .root_source_file = plutuz_dep.path("src/root.zig"),
        .target = target,
    });
    plutuz_mod.addIncludePath(blst_dep.path("bindings"));
    plutuz_mod.linkLibrary(blst_lib);

    // FFI module (our code)
    const ffi_mod = b.createModule(.{
        .root_source_file = b.path("ffi.zig"),
        .target = target,
        .optimize = .ReleaseFast,
        .imports = &.{
            .{ .name = "plutuz", .module = plutuz_mod },
        },
    });
    ffi_mod.addIncludePath(blst_dep.path("bindings"));
    ffi_mod.linkLibrary(blst_lib);

    const ffi_lib = b.addLibrary(.{
        .linkage = .static,
        .name = "plutuz_ffi",
        .root_module = ffi_mod,
    });
    b.installArtifact(ffi_lib);
    b.installArtifact(blst_lib);
}
