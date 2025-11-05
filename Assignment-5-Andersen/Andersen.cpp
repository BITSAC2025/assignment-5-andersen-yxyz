/**
 * Andersen.cpp
 * @author kisslune
 */

#include "A5Header.h"

using namespace llvm;
using namespace std;

int main(int argc, char** argv)
{
    auto moduleNameVec =
            OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                     "[options] <input-bitcode...>");

    SVF::LLVMModuleSet::buildSVFModule(moduleNameVec);

    SVF::SVFIRBuilder builder;
    auto pag = builder.build();
    auto consg = new SVF::ConstraintGraph(pag);
    consg->dump();

    Andersen andersen(consg);

    // TODO: complete the following method
    andersen.runPointerAnalysis();

    andersen.dumpResult();
    SVF::LLVMModuleSet::releaseLLVMModuleSet();
	return 0;
}


void Andersen::runPointerAnalysis()
{
    // TODO: complete this method. Point-to set and worklist are defined in A5Header.h
    //  The implementation of constraint graph is provided in the SVF library
    
    WorkList<unsigned> worklist;
    
    // Initialize: process all address constraints (*p = &a)
    // Address constraints initialize the point-to sets
    for (auto it = consg->begin(); it != consg->end(); ++it)
    {
        SVF::ConstraintEdge* edge = *it;
        if (edge->getEdgeKind() == SVF::ConstraintEdge::Addr)
        {
            unsigned src = edge->getSrcID();
            unsigned dst = edge->getDstID();
            // Add address to point-to set: pts(src) = {dst}
            if (pts[src].insert(dst).second)
            {
                worklist.push(src);
            }
        }
    }
    
    // Iteratively process constraints until worklist is empty
    while (!worklist.empty())
    {
        unsigned p = worklist.pop();
        
        // Process copy constraints: p = q
        for (auto it = consg->begin(); it != consg->end(); ++it)
        {
            SVF::ConstraintEdge* edge = *it;
            if (edge->getEdgeKind() == SVF::ConstraintEdge::Copy)
            {
                unsigned src = edge->getSrcID();
                unsigned dst = edge->getDstID();
                
                if (dst == p)
                {
                    // Copy constraint: src = dst, propagate pts(dst) to pts(src)
                    bool changed = false;
                    for (unsigned pointee : pts[dst])
                    {
                        if (pts[src].insert(pointee).second)
                        {
                            changed = true;
                        }
                    }
                    if (changed)
                    {
                        worklist.push(src);
                    }
                }
            }
        }
        
        // Process load constraints: p = *q
        for (auto it = consg->begin(); it != consg->end(); ++it)
        {
            SVF::ConstraintEdge* edge = *it;
            if (edge->getEdgeKind() == SVF::ConstraintEdge::Load)
            {
                unsigned src = edge->getSrcID();
                unsigned dst = edge->getDstID();
                
                if (dst == p)
                {
                    // Load constraint: src = *dst, for each o in pts(dst), propagate pts(o) to pts(src)
                    bool changed = false;
                    for (unsigned o : pts[dst])
                    {
                        for (unsigned pointee : pts[o])
                        {
                            if (pts[src].insert(pointee).second)
                            {
                                changed = true;
                            }
                        }
                    }
                    if (changed)
                    {
                        worklist.push(src);
                    }
                }
            }
        }
        
        // Process store constraints: *p = q
        for (auto it = consg->begin(); it != consg->end(); ++it)
        {
            SVF::ConstraintEdge* edge = *it;
            if (edge->getEdgeKind() == SVF::ConstraintEdge::Store)
            {
                unsigned src = edge->getSrcID();
                unsigned dst = edge->getDstID();
                
                if (src == p)
                {
                    // Store constraint: *src = dst, for each o in pts(src), propagate pts(dst) to pts(o)
                    bool changed = false;
                    for (unsigned o : pts[src])
                    {
                        for (unsigned pointee : pts[dst])
                        {
                            if (pts[o].insert(pointee).second)
                            {
                                changed = true;
                            }
                        }
                    }
                    if (changed)
                    {
                        // Add all objects in pts(src) to worklist
                        for (unsigned o : pts[src])
                        {
                            worklist.push(o);
                        }
                    }
                }
            }
        }
    }
}