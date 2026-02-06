plugins {
    kotlin("jvm") version "2.1.21"
    application
}

group = "ru.mylogininya"
version = "1.0-SNAPSHOT"

repositories {
    mavenCentral()
}

application {
    mainClass.set("ru.mylogininya.MainKt")
}

dependencies {
    implementation("it.unimi.dsi:fastutil-core:8.5.12")
    testImplementation(kotlin("test"))
}

tasks.test {
    useJUnitPlatform()
}
kotlin {
    jvmToolchain(22)
}