#include <math.h>

int sphere_x = 10;
int sphere_y = 10;

void setUnitSphere(Mesh & o_mesh, int nX = 10, int nY = 10)
{
    o_mesh.vertices.clear();
    o_mesh.normals.clear();
    o_mesh.triangles.clear();

    const float step_theta = M_PI*2. / (float) nY;
    const float begin_theta = 0.;

    const float step_phi = M_PI / (float) nX;
    const float begin_phi = - M_PI_2;

    const Vec3 poleNord = Vec3(0, 0, -1);
    const Vec3 poleSud = Vec3(0, 0, 1);

    // Index 0
    o_mesh.vertices.push_back(poleNord);

    for (int i = 0; i < nX - 1; ++i) {
        for (int j = 0; j < nY; ++j) {
            const float phi = begin_phi + (i + 1)*step_phi;
            const float theta = begin_theta + j*step_theta;

            const float x = cos(theta)*cos(phi);
            const float y = sin(theta)*cos(phi);
            const float z = sin(phi);

            const Vec3 vertex = Vec3(x, y, z);

            // Index i * nY + j + 1
            o_mesh.vertices.push_back(vertex);
        }
    }

    // Index (nX - 1) * nY + 1
    o_mesh.vertices.push_back(poleSud);

    // Triangles du pole nord
    for (int i = 0; i < nY; ++i) {
        const int a = 0;
        const int b = i + 1;
        const int c = b % nY + 1;

        const Triangle triangle = Triangle(a, c, b);
        o_mesh.triangles.push_back(triangle);
    }

    // Triangles
    for (int i = 0; i < nX - 2; ++i) {
        for (int j = 0; j < nY; ++j) {
            const int a = j + 1 + nY*i;
            const int b = a % nY + 1 + nY*i;
            const int c = a + nY;
            const int d = b + nY;

            const Triangle triangle1 = Triangle(a, b, d);
            const Triangle triangle2 = Triangle(a, d, c);

            o_mesh.triangles.push_back(triangle1);
            o_mesh.triangles.push_back(triangle2);
        }
    }

    // Triangles du pole sud
    for (int i = 0; i < nY; ++i) {
        const int a = (nX - 1) * nY + 1;
        const int b = a - i - 1;
        const int c = b % nY + (nX - 2) * nY + 1;

        const Triangle triangle = Triangle(a, b, c);
        o_mesh.triangles.push_back(triangle);
    }

    // Normales
    const float norm = sqrt(poleNord[0] * poleNord[0] + poleNord[1] * poleNord[1] + poleNord[2] * poleNord[2]);
    for (const Vec3& v : o_mesh.vertices) {
        o_mesh.normals.push_back(v/norm);
    }
}

void key (unsigned char keyPressed, int x, int y) {
    switch (keyPressed) {
        // ...
        case '-':
            setUnitSphere(unit_sphere, (--sphere_x < 5) ? ++sphere_x : sphere_x, (--sphere_y < 5) ? ++sphere_y : sphere_y);
            break;

        case '+':
            setUnitSphere(unit_sphere, ++sphere_x, ++sphere_y);
            break;

        default:
            break;
    }
    idle ();
}