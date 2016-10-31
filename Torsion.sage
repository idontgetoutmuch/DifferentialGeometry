M = Manifold(2, 'M', start_index=1)
X.<x,y> = M.chart()
nab = M.affine_connection('nabla', latex_name=r'\nabla')
ch_basis = M.automorphism_field()
ch_basis[1,1], ch_basis[2,2] = 1, 1/sin(x)
e = M.default_frame().new_frame(ch_basis, 'e')
nab.add_coef(e)
# nab.connection_form(1,1,e)
eX = X.frame()

N = Manifold(2, 'N', start_index=1)
X.<x,y> = N.chart()
merc_nab = N.affine_connection('merc_nabla', latex_name=r'\nabla_m')
merc_basis = N.automorphism_field()
merc_basis[1,1], merc_basis[2,2] = 1, 1/sin(x)

m = N.default_frame().new_frame(merc_basis, 'm')
m[1][:], m[2][:]
mf = m.coframe()
mf[1][:], mf[2][:]

merc_nab.add_coef(m)
merc_nab.display(m)
merc_nab.display()

merc_nab.torsion_form(2,m)[:]
merc_nab.torsion_form(1,m)[:]
merc_nab.torsion_form(1)[:]
merc_nab.torsion_form(2)[:]

t = merc_nab.torsion()
t[:]

merc_nab.curvature_form(1,1).display()
merc_nab.curvature_form(1,2).display()
merc_nab.curvature_form(2,1).display()
merc_nab.curvature_form(2,2).display()
merc_nab.curvature_form(1,1,m).display()
merc_nab.curvature_form(1,2,m).display()
merc_nab.curvature_form(2,1,m).display()
merc_nab.curvature_form(2,2,m).display()

g = N.metric('g') ; g
h = M.metric('h'); h
h[1,1] =  1 / ((sin(x))^2)
h[2,2] = 1
nabla_h = h.connection(); nabla_h
riem_h = h.riemann() ; riem_h
t_h = nabla_h.torsion(); t_h

N = Manifold(2, 'N',r'\mathcal{N}', start_index=1)
c_n_x_y.<x,y> = N.chart()
f_n_x_y = c_n_x_y.frame()
c_n_r_theta.<r,theta> = N.chart()
f_n_r_theta = c_n_r_theta.frame()
n_x_y_to_r_theta = c_n_x_y.transition_map(c_n_r_theta, (sqrt(x^2 + y^2), arctan(y/x)))
print(n_x_y_to_r_theta)
print(n_x_y_to_r_theta.display())
n_x_y_to_r_theta.set_inverse(r * cos(theta), r * sin(theta))
g_e = N.metric('g_e')
g_e[1,1], g_e[2,2] = 1, 1
print(g_e.display(f_n_x_y))
nab_e = g_e.connection()
print(nab_e)
print(nab_e.display(f_n_x_y))
print(nab_e.display(f_n_r_theta))
