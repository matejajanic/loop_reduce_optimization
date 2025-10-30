add_llvm_library( LLVMOurLoopReduce MODULE BUILDTREE_ONLY
  OurLoopReduce.cpp

  DEPENDS
  intrinsics_gen
  PLUGIN_TOOL
  opt
  )
