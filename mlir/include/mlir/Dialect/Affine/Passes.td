//===-- Passes.td - Affine pass definition file ------------*- tablegen -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file contains definitions for passes within the Affine/ directory.
//
//===----------------------------------------------------------------------===//

#ifndef MLIR_DIALECT_AFFINE_PASSES
#define MLIR_DIALECT_AFFINE_PASSES

include "mlir/Pass/PassBase.td"

def AffineDataCopyGeneration : FunctionPass<"affine-data-copy-generate"> {
  let summary = "Generate explicit copying for affine memory operations";
  let constructor = "mlir::createAffineDataCopyGenerationPass()";
  let dependentDialects = ["memref::MemRefDialect"];
  let options = [
    Option<"fastMemoryCapacity", "fast-mem-capacity", "uint64_t",
           /*default=*/"std::numeric_limits<uint64_t>::max()",
           "Set fast memory space capacity in KiB (default: unlimited)">,
    Option<"fastMemorySpace", "fast-mem-space", "unsigned",
           /*default=*/"1",
           "Fast memory space identifier for copy generation (default: 1)">,
    Option<"generateDma", "generate-dma", "bool",
           /*default=*/"true", "Generate DMA instead of point-wise copy">,
    Option<"minDmaTransferSize", "min-dma-transfer", "int",
           /*default=*/"1024",
           "Minimum DMA transfer size supported by the target in bytes">,
    Option<"slowMemorySpace", "slow-mem-space", "unsigned",
           /*default=*/"0",
           "Slow memory space identifier for copy generation (default: 0)">,
    Option<"skipNonUnitStrideLoops", "skip-non-unit-stride-loops", "bool",
           /*default=*/"false", "Testing purposes: avoid non-unit stride loop "
                                "choice depths for copy placement">,
    Option<"tagMemorySpace", "tag-mem-space", "unsigned",
           /*default=*/"0",
           "Tag memory space identifier for copy generation (default: 0)">,
  ];
}

def AffineLoopInvariantCodeMotion
    : FunctionPass<"affine-loop-invariant-code-motion"> {
  let summary = "Hoist loop invariant instructions outside of affine loops";
  let constructor = "mlir::createAffineLoopInvariantCodeMotionPass()";
}

def AffineLoopTiling : FunctionPass<"affine-loop-tile"> {
  let summary = "Tile affine loop nests";
  let constructor = "mlir::createLoopTilingPass()";
  let options = [
    Option<"cacheSizeInKiB", "cache-size", "uint64_t", /*default=*/"512",
           "Set size of cache to tile for in KiB">,
    Option<"separate", "separate", "bool", /*default=*/"",
           "Separate full and partial tiles">,
    Option<"tileSize", "tile-size", "unsigned", /*default=*/"",
           "Use this tile size for all loops">,
    ListOption<"tileSizes", "tile-sizes", "unsigned",
               "List of tile sizes for each perfect nest "
               "(overridden by -tile-size)",
               "llvm::cl::ZeroOrMore">,
  ];
}

def AffineLoopUnroll : FunctionPass<"affine-loop-unroll"> {
  let summary = "Unroll affine loops";
  let constructor = "mlir::createLoopUnrollPass()";
  let options = [
    Option<"unrollFactor", "unroll-factor", "unsigned", /*default=*/"4",
           "Use this unroll factor for all loops being unrolled">,
    Option<"unrollUpToFactor", "unroll-up-to-factor", "bool",
           /*default=*/"false", "Allow unrolling up to the factor specified">,
    Option<"unrollFull", "unroll-full", "bool", /*default=*/"false",
           "Fully unroll loops">,
    Option<"numRepetitions", "unroll-num-reps", "unsigned", /*default=*/"1",
           "Unroll innermost loops repeatedly this many times">,
    Option<"unrollFullThreshold", "unroll-full-threshold", "unsigned",
           /*default=*/"1",
           "Unroll all loops with trip count less than or equal to this">,
  ];
}

def AffineLoopUnrollAndJam : FunctionPass<"affine-loop-unroll-jam"> {
  let summary = "Unroll and jam affine loops";
  let constructor = "mlir::createLoopUnrollAndJamPass()";
  let options = [
    Option<"unrollJamFactor", "unroll-jam-factor", "unsigned",
           /*default=*/"4",
           "Use this unroll jam factor for all loops (default 4)">,
  ];
}

def AffineScalarReplacement : FunctionPass<"affine-scalrep"> {
  let summary = "Replace affine memref acceses by scalars by forwarding stores "
                "to loads and eliminating redundant loads";
  let description = [{
    This pass performs store to load forwarding and redundant load elimination
    for affine memref accesses and potentially eliminates the entire memref
    if all its accesses are forwarded.

    Input

    ```mlir
    func @store_load_affine_apply() -> memref<10x10xf32> {
      %cf7 = constant 7.0 : f32
      %m = alloc() : memref<10x10xf32>
      affine.for %i0 = 0 to 10 {
        affine.for %i1 = 0 to 10 {
          affine.store %cf7, %m[%i0, %i1] : memref<10x10xf32>
          %v0 = affine.load %m[%i0, %i1] : memref<10x10xf32>
          %v1 = arith.addf %v0, %v0 : f32
        }
      }
      return %m : memref<10x10xf32>
    }
    ```

    Output

    ```mlir
    module {
      func @store_load_affine_apply() -> memref<10x10xf32> {
        %cst = constant 7.000000e+00 : f32
        %0 = alloc() : memref<10x10xf32>
        affine.for %arg0 = 0 to 10 {
          affine.for %arg1 = 0 to 10 {
            affine.store %cst, %0[%arg0, %arg1] : memref<10x10xf32>
            %1 = arith.addf %cst, %cst : f32
          }
        }
        return %0 : memref<10x10xf32>
      }
    }
    ```
  }];
  let constructor = "mlir::createAffineScalarReplacementPass()";
}

def AffineVectorize : FunctionPass<"affine-super-vectorize"> {
  let summary = "Vectorize to a target independent n-D vector abstraction";
  let constructor = "mlir::createSuperVectorizePass()";
  let dependentDialects = ["vector::VectorDialect"];
  let options = [
    ListOption<"vectorSizes", "virtual-vector-size", "int64_t",
               "Specify an n-D virtual vector size for vectorization",
               "llvm::cl::ZeroOrMore, llvm::cl::MiscFlags::CommaSeparated">,
    // Optionally, the fixed mapping from loop to fastest varying MemRef
    // dimension for all the MemRefs within a loop pattern:
    //   the index represents the loop depth, the value represents the k^th
    //   fastest varying memory dimension.
    // This is voluntarily restrictive and is meant to precisely target a
    // particular loop/op pair, for testing purposes.
    ListOption<"fastestVaryingPattern", "test-fastest-varying", "int64_t",
               "Specify a 1-D, 2-D or 3-D pattern of fastest varying memory "
               "dimensions to match. See defaultPatterns in Vectorize.cpp for "
               "a description and examples. This is used for testing purposes",
               "llvm::cl::ZeroOrMore, llvm::cl::MiscFlags::CommaSeparated">,
    Option<"vectorizeReductions", "vectorize-reductions", "bool",
           /*default=*/"false",
           "Vectorize known reductions expressed via iter_args. "
           "Switched off by default.">
  ];
}

def AffineParallelize : FunctionPass<"affine-parallelize"> {
  let summary = "Convert affine.for ops into 1-D affine.parallel";
  let constructor = "mlir::createAffineParallelizePass()";
  let options = [
    Option<"maxNested", "max-nested", "unsigned", /*default=*/"-1u",
           "Maximum number of nested parallel loops to produce. "
           "Defaults to unlimited (UINT_MAX).">,
    Option<"parallelReductions", "parallel-reductions", "bool",
           /*default=*/"false",
           "Whether to parallelize reduction loops. Defaults to false.">
  ];
}

def AffineLoopNormalize : FunctionPass<"affine-loop-normalize"> {
  let summary = "Apply normalization transformations to affine loop-like ops";
  let constructor = "mlir::createAffineLoopNormalizePass()";
}

def SimplifyAffineStructures : FunctionPass<"simplify-affine-structures"> {
  let summary = "Simplify affine expressions in maps/sets and normalize "
                "memrefs";
  let constructor = "mlir::createSimplifyAffineStructuresPass()";
}

#endif // MLIR_DIALECT_AFFINE_PASSES
