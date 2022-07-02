# import os
class BooleanAlgebraSolver:
    def __init__(self, swap=None):
        
        # print(os.getcwd())
        if swap is None:
            self.swap = True
        self.num_vars  = 0
        self.variables = {}


    def make_partial_var(self, var):

        var_id = abs(var)
        num_vars = self.num_vars
        val = var//var_id

        if num_vars == 0 or var_id > num_vars:
            print("more variables than normal")

        if self.swap: var_id = num_vars+1-var_id

        # print("var",var)
        # val = var//var_id
        # print("val", val)
        if val == -1:
            return 1 << ((var_id-1) * 2 + 1)
        elif val == 1:
            return 1 << ((var_id-1) * 2)


    def _line_to_cube(self, line:str):
        num_vars, swap = self.num_vars, self.swap

        line = line.split()

        all_1s = int("1"*2*num_vars, 2)
        this_cube = all_1s

        for var_id in line[1:]:
            var_id = int(var_id)
            this_cube = this_cube & ~(self.make_partial_var(-var_id))
        
        return this_cube


    def read_sop_function(self, file_path, func_id):
        swap = self.swap
        with open(file_path, 'r') as f: 
            num_vars = int(next(f).strip())

            if not self.num_vars:
                self.num_vars = num_vars
            
            elif num_vars != self.num_vars:
                print("warning: more variables than normal")

            num_cubes = int(next(f).strip())

            cube_list = []
            for cube in range(num_cubes):
                this_line = next(f)
                this_cube = self._line_to_cube(this_line)
                cube_list.append(this_cube)
        
        self.variables[func_id] = cube_list

    def make_variable_filter(self, var_id):
        swap = self.swap
        return self.make_partial_var(var_id) | self.make_partial_var(-var_id)

    def possible_states(self, var_id):
        num_vars, swap = self.num_vars, self.swap
        return {"01": (p := self.make_partial_var(var_id,)),
                "10": (n := self.make_partial_var(-var_id)),
                "11": p | n
        }

    def retrieve_partial_var(self, cube, var_id):
        key = self.make_variable_filter(var_id)
        return cube & key

    
    def presence_count(self, var_id, cube_list):
        num_vars, swap = self.num_vars, self.swap
        states = self.possible_states(var_id)
        
        positive_key, complement_key, select_key = states["01"], states["10"], states["11"]

        positive_count , complement_count = 0, 0

        for cube in cube_list:
            if cube & select_key == positive_key: 
                positive_count += 1
            elif cube & select_key == complement_key:
                complement_count += 1
        
        return (positive_count, complement_count)
    
    
    def find_most_unate(self, cube_list):
        num_vars = self.num_vars
        presence_count_list = [(var_id, self.presence_count(var_id, cube_list)) for var_id in range(1, num_vars+1)]
        presence_count_list.sort(key = lambda x: [-(x[1][0] + x[1][1]), abs(x[1][0] - x[1][1]), x[0]])
        return presence_count_list[0][0]
    

    def cofactor(self, cube, var):
        val = var / abs(var)
        var_id = abs(var)
        states = self.possible_states(var_id)
        present_positive, present_complement, select_key = states['01'], states['10'], states['11']

        curr_val = select_key & cube
    
        if val == -1 and curr_val == present_positive:
            return 0
        elif val == 1 and curr_val == present_complement:
            return 0
        else:
            return cube | select_key

    def OR (self, cube_list_1, cube_list_2, *, dest_id=None): 
        #TODO : make dest_id keyword only
        or_cube_list = list(cube_list_1)
        or_cube_list.extend(cube_list_2)

        if dest_id is not None:
            self.variables[dest_id] = or_cube_list
        return or_cube_list
    

    def cube_list_cofactor(self, cube_list, var):

        ret_cube_list = [self.cofactor(cube, var) for cube in cube_list]
        ret_cube_list = [val for val in ret_cube_list if val != 0]
        return ret_cube_list

    def de_morgan (self, cube):
        num_vars = self.num_vars
        cube_list = []
        all_1s = 2 ** (num_vars* 2) - 1
        for var_id in range(1, num_vars+1):
            this_var = self.retrieve_partial_var(cube, var_id)

            if this_var == (x:= self.make_partial_var(-var_id)):
                cube_list.append( all_1s & ~x)
            elif this_var == (x:= self.make_partial_var(var_id)):
                cube_list.append(all_1s & ~x)
            else:
                continue
        return cube_list
    

    def single_AND(self, var, cube_list):
        var_id = abs(var)
        var = self.make_partial_var(-var)
        new_cube_list = [ x for cube in cube_list if (x:= ~var & cube) & self.make_variable_filter(var_id)  in (self.make_partial_var(var_id), self.make_partial_var(-var_id))]
        return new_cube_list

    def urp_inverse(self, cube_list, *, dest_id=None):

        all_1s = 2 ** (self.num_vars*2) - 1
        if not cube_list:
            
            return [all_1s]
        
        cube_list.sort(reverse=True)

        if cube_list[0] == all_1s: 
            return []

        elif len(cube_list) == 1: 
            return self.de_morgan(cube_list[0])
        
        else:
            most_unate = self.find_most_unate(cube_list)

            P = self.urp_inverse(self.cube_list_cofactor(cube_list, most_unate))
            P = self.single_AND(most_unate, P)

            N = self.urp_inverse( self.cube_list_cofactor(cube_list, -most_unate))
            N = self.single_AND(-most_unate, N)

            result = self.OR(P, N)

            if dest_id: 
                self.variables[dest_id] = result
            
            return result


    def AND(self,  cube1, cube2, * , dest_id=None):

        not_cube1 = self.urp_inverse(cube1)
        not_cube2 = self.urp_inverse(cube2)

        result = self.urp_inverse(self.OR(not_cube1, not_cube2))

        if dest_id:
            self.variables[dest_id] = result
        
        return result

        # for the sake of ease with reading the variables, reverse variable ids

    def write_function(self, func_id, file_path):
        num_vars = self.num_vars
        cube_list = self.variables[func_id]

        with open(file_path, "w") as f: 
            f.write(str(num_vars) + "\n")
            f.write(str(len(cube_list)) + "\n")


            format_bin = "{:0>" + str(num_vars * 2) + "b}"

            for cube in cube_list:
                this_line = []
                this_cube = format_bin.format(cube)
                for val in range(0, num_vars):
                    this_var = this_cube[2*val:2*val+2]

                    val+=1
                    val = str(val)
                    if this_var == "01":
                        this_line.append(val)
                    elif this_var == "10":
                        this_line.append("-" + val)


                this_line = str(len(this_line)) + " " + " ".join(str(var) for var in this_line)
                f.write(this_line + "\n")

    def evaluate_file(self, file_path):
        self.file_name = file_path
        with open(file_path, 'r') as f:

            for line in f: self.evaluate_line(line)


    def evaluate_line(self, line):
        line = line.split()
        cmd = line[0]

        if cmd == "q":
            return
        
        elif cmd == 'p':
            self.write_function(line[1], self.file_name+".out"+".txt")
            return
        
        elif cmd == 'r':
            self.read_sop_function(line[1] + ".pcn", line[1])
            return

        elif cmd == "!":
            self.urp_inverse(self.variables[line[2]], dest_id = line[1])
            return

        dest, source1, source2 = line[1:]
        source1, source2 = self.variables[source1], self.variables[source2]

        if cmd == "&":
            self.AND(source1, source2, dest_id=dest)
            return

        elif cmd == "+":
            self.OR(source1, source2, dest_id=dest)
            return
        
        else:
            return



if __name__ == "__main__":

    # a = make_partial_var(1, 4)
    # assert a == int("0001", 2)
    # b = make_partial_var(-1, 4)
    # assert b == int("0010", 2)
    # assert b == a + 1
    # assert a | b == int("0011", 2)


    # c1 = line_to_cube("2 1 2", 2)
    # assert c1 == int("0101", 2)
    # c2 = line_to_cube("1 1", 3)
    # assert c2 == int("011111",2)

    test_solver = BooleanAlgebraSolver()
    test_solver.read_sop_function(r"C:\Users\HP\Documents\courses\vlsi_cad_1_coursera\ProgrammingAssignment1Files\ProgrammingAssignment1Files\BooleanCalculatorEngine\1.pcn", 1)
    
    test_solver2 = BooleanAlgebraSolver()

    for input_file in range(2, 3):
        test_solver2 = BooleanAlgebraSolver()
        test_solver2.evaluate_file(f"cmd{str(input_file)}.txt")