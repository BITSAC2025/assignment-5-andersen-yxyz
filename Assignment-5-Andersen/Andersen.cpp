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
    
    // Initialize: process all address constraints (p = &o)
    // Address constraints: o --Addr--> p, meaning o ∈ pts(p)
    // In ConstraintGraph: src is object o, dst is pointer p
    for (auto it = consg->begin(); it != consg->end(); ++it)
    {
        SVF::ConstraintEdge* edge = *it;
        if (edge->getEdgeKind() == SVF::ConstraintEdge::Addr)
        {
            unsigned src = edge->getSrcID();  // object o
            unsigned dst = edge->getDstID();   // pointer p
            // Add object to point-to set: o ∈ pts(p)
            if (pts[dst].insert(src).second)
            {
                worklist.push(dst);
            }
        }
    }
    
    // Iteratively process constraints until worklist is empty
    while (!worklist.empty())
    {
        unsigned p = worklist.pop();
        
        // Process copy constraints: q = p
        // Copy constraint: p --Copy--> q, meaning pts(p) ⊆ pts(q)
        // When pts(p) is updated, propagate to pts(q)
        for (auto it = consg->begin(); it != consg->end(); ++it)
        {
            SVF::ConstraintEdge* edge = *it;
            if (edge->getEdgeKind() == SVF::ConstraintEdge::Copy)
            {
                unsigned src = edge->getSrcID();  // pointer p
                unsigned dst = edge->getDstID();   // pointer q
                
                if (src == p)
                {
                    // Copy constraint: propagate pts(p) to pts(q)
                    bool changed = false;
                    for (unsigned pointee : pts[p])
                    {
                        if (pts[dst].insert(pointee).second)
                        {
                            changed = true;
                        }
                    }
                    if (changed)
                    {
                        worklist.push(dst);
                    }
                }
            }
        }
        
        // Process load constraints: q = *p
        // Load constraint: p --Load--> q, meaning ∀o ∈ pts(p): pts(o) ⊆ pts(q)
        // When pts(p) is updated, for each o in pts(p), propagate pts(o) to pts(q)
        for (auto it = consg->begin(); it != consg->end(); ++it)
        {
            SVF::ConstraintEdge* edge = *it;
            if (edge->getEdgeKind() == SVF::ConstraintEdge::Load)
            {
                unsigned src = edge->getSrcID();  // pointer p
                unsigned dst = edge->getDstID();   // pointer q
                
                if (src == p)
                {
                    // Load constraint: for each o in pts(p), propagate pts(o) to pts(q)
                    bool changed = false;
                    for (unsigned o : pts[p])
                    {
                        for (unsigned pointee : pts[o])
                        {
                            if (pts[dst].insert(pointee).second)
                            {
                                changed = true;
                            }
                        }
                    }
                    if (changed)
                    {
                        worklist.push(dst);
                    }
                }
            }
        }
        
        // Process store constraints: *p = q
        // Store constraint: q --Store--> p, meaning ∀o ∈ pts(p): pts(q) ⊆ pts(o)
        // When pts(p) is updated, for each o in pts(p), propagate pts(q) to pts(o)
        // When pts(q) is updated, for each o in pts(p), propagate pts(q) to pts(o)
        for (auto it = consg->begin(); it != consg->end(); ++it)
        {
            SVF::ConstraintEdge* edge = *it;
            if (edge->getEdgeKind() == SVF::ConstraintEdge::Store)
            {
                unsigned src = edge->getSrcID();  // pointer q
                unsigned dst = edge->getDstID();  // pointer p
                
                if (dst == p)
                {
                    // Store constraint: for each o in pts(p), propagate pts(q) to pts(o)
                    bool changed = false;
                    for (unsigned o : pts[p])
                    {
                        for (unsigned pointee : pts[src])
                        {
                            if (pts[o].insert(pointee).second)
                            {
                                changed = true;
                            }
                        }
                    }
                    if (changed)
                    {
                        // Add all objects in pts(p) to worklist
                        for (unsigned o : pts[p])
                        {
                            worklist.push(o);
                        }
                    }
                }
                else if (src == p)
                {
                    // When pts(q) is updated, propagate to all objects o in pts(p)
                    bool changed = false;
                    for (unsigned o : pts[dst])
                    {
                        for (unsigned pointee : pts[p])
                        {
                            if (pts[o].insert(pointee).second)
                            {
                                changed = true;
                            }
                        }
                    }
                    if (changed)
                    {
                        // Add all objects in pts(dst) to worklist
                        for (unsigned o : pts[dst])
                        {
                            worklist.push(o);
                        }
                    }
                }
            }
        }
    }
}