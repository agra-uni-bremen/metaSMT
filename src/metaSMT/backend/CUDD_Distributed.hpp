#include "CUDD_Context.hpp"
#include <cstdlib>

#include <boost/format.hpp>
#include <boost/random/uniform_int.hpp>
#include <boost/random/mersenne_twister.hpp>

namespace metaSMT {
  namespace solver {

class CUDD_Distributed : public CUDD_Context
{
			
public: 

	CUDD_Distributed ()
  : CUDD_Context()
  , previous(_manager.bddZero())
  {
	  reset();
	}

	bool solve() {
 	 	BDD complete =_assertions & _assumptions;  
    if ( previous != complete) {
      //std::cout << "resetting distribution cache" << std::endl;
			reset();
      previous = complete;
    } else {
      //std::cout << "keeping distribution cache" << std::endl;
    }
	 	bool  ret =  complete != _manager.bddZero();
         	_assumptions = _manager.bddOne();
        	//printDD(complete.getNode(),"BDD.dot");
	        if(ret) {
			store_solution( complete.getNode() );
		}
		return ret;
	}

private:
	std::map<DdNode *, unsigned> map_0;
	std::map<DdNode *, unsigned> map_1;
	
	void reset() {

		map_0.clear();
		map_1.clear();

		map_0 [_manager.bddZero().getNode()] = 1;
		map_1 [_manager.bddZero().getNode()] = 0;
		map_0 [_manager.bddOne().getNode()] = 0;
		map_1 [_manager.bddOne().getNode()] = 1;
	}
	unsigned distance(DdNode *parent, DdNode *child) {
		int i_1 = Cudd_ReadPerm(_manager.getManager(),Cudd_Regular(parent)->index);
		int i_2 = (Cudd_IsConstant(child)) ? _manager.ReadSize() : Cudd_ReadPerm(_manager.getManager(), Cudd_Regular(child)->index);	
		//std::cout << boost::format( "distance(v%d,v%d) = %d - %d = %d\n") 
		//	% parent->index % child->index % i_2 % i_1 % (i_2 - i_1);
		return i_2 - i_1;
	}

	unsigned skipped ( DdNode *parent, DdNode *child) {
		unsigned t = distance (parent, child);
		if(t > 0) return t-1;
		else return 0;
	}

	unsigned count_0 (DdNode *root) {
		if( Cudd_IsComplement(root)) {
			DdNode * comp = Cudd_Regular(root);
 			//std::cout << boost::format("count_0(v%d)=count_1( ~v%d )\n") % root->index% comp->index;
			return count_1(comp);
		}
		//std::cout << boost::format("count_0(v%d)\n") % root->index;
		std::map<DdNode *, unsigned>::iterator iter = map_0.find(root); 
	 	if(iter != map_0.end()) {
		   	//std::cout << boost::format("count_0(v%d) = %d\n") % root->index % iter->second;
			return iter->second;
		} else {
			
			unsigned ret = count_0 ( Cudd_T( root ) )*( 1ull << skipped( root, Cudd_T(root) ) ) ;
			//std::cout << "then count is " << ret << std::endl;
		   	ret += count_0 (Cudd_E(root)) *  ( 1ull << skipped( root, Cudd_E( root ) ) );
			//std::cout << "after else count is " << ret << std::endl;
		   	map_0.insert( std::make_pair(root,ret) );
			//std::cout << boost::format("count_0(v%d) = %d\n") % root->index % ret;
		   	return ret;
		}			
	}

	unsigned count_1 (DdNode *root) {
		if( Cudd_IsComplement(root)) {
			DdNode * comp = Cudd_Regular(root);
 			//std::cout << boost::format("count_1(v%d)=count_0( ~v%d )\n") % root->index% comp->index;
			return count_0(comp);
		}
		//std::cout << boost::format("count_1(v%d)\n") % root->index;
		std::map<DdNode *, unsigned>::iterator iter = map_1.find(root); 
	 
	if(iter != map_1.end()) {
		   //std::cout << boost::format("count_1(v%d) = %d\n") % root->index % iter->second;
		  return iter->second;
		} else {
		     	unsigned ret = count_1 ( Cudd_T( root ) )*( 1ull << skipped( root, Cudd_T(root) ) ) ;
			//std::cout << "then count is " << ret << std::endl;
		   	ret += count_1 (Cudd_E(root)) *  ( 1ull << skipped( root, Cudd_E( root ) ) );
			//std::cout << "after else count is " << ret << std::endl;

		   map_1.insert( std::make_pair(root,ret) );
	           //std::cout << boost::format("count_1(v%d) = %d\n") % root->index % ret;
		   return ret;
		
	         }
	}


	void store_solution ( DdNode * root) {

	   // clear solution
            unsigned size = _manager.ReadSize();
	    std::vector< boost::logic::tribool > (size, boost::logic::indeterminate).swap(_solution);

	    bool negated = false;
	   
            while( ! Cudd_IsConstant(root) ) {
         	
		//std::cout << "chosing for v" << root->index << " (negated: " << negated << ")" << std::endl;
		
		unsigned cnt_r = 0;
		unsigned cnt_t = 0;
		negated ^= Cudd_IsComplement( root );
		root = Cudd_Regular(root);
		DdNode* child = Cudd_T(root);
		if( negated ) {
			cnt_r = count_0(root);
			cnt_t = count_0(child) << skipped(root, child);
		} else {
			cnt_r = count_1(root);
			cnt_t = count_1(child)<< skipped(root, child);
		}
		
		//std::cout << "count: " << cnt_r << " " << cnt_t << std::endl;

      		boost::uniform_int<unsigned> rnd( 0, cnt_r-1);
		unsigned select = rnd(gen);
		//std::cout << boost::format("%u %u %u") %select%cnt_r%cnt_t << std::endl; 
		if(select <  cnt_t )
		{			
			//std::cout << "v" << root->index << " = 1" << std::endl;
			_solution[root->index] = true;
			root = Cudd_T( root );
		}	
		else
		{
			//std::cout << "v" << root->index << " = 0" << std::endl;
			_solution[root->index] = false;
			root = Cudd_E( root );	
		}
	    }
	    assert( Cudd_V(root) == 1 );  
	}
	
  void printDD(DdNode *root, std::string fileName) {
    FILE *file = fopen(fileName.c_str(),"w");

    char **iname = (char**) malloc(sizeof(char *)*_manager.ReadSize());
    for(unsigned i = 0; i < (unsigned)_manager.ReadSize(); ++i)
    {
      char *name = (char*) malloc(256);
      sprintf(name,"v%d", _manager.bddVar(i).NodeReadIndex());
      iname [i] = name;
    }
    //extern int Cudd_DumpDot (DdManager *dd, int n, DdNode **f, char **inames, char **onames, FILE *fp);
    Cudd_DumpDot (_manager.getManager(),1,&root,iname, NULL,file);
    fclose(file);	
  }
    protected:
      boost::mt19937 gen;

    private:
      BDD previous;
    }; // class CUDD_Distribuded

  }//  namespace solver
} //namespace metaSMT
